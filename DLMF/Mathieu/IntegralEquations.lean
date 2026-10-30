/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SpectralExistence
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import DLMF.Mathieu.Properties

/-!
# Integral equations (DLMF §28.10)

The integral equations 28.10.1–28.10.8 with elementary kernels (`q = h²`, real `h`, so
`q ≥ 0`; the notation `A^n_m`, `B^n_m` is that of §28.4) and 28.10.9–28.10.10 with the Bessel
kernel `J₀` (Mathlib's `Complex.besselJ 0`; `J₀(2√w)` is entire in `w`, so the branch of the
square root in 28.10.9 is immaterial — the principal one is used). All ten were checked
numerically (`h = 1.3`, `z = 0.4`, `n ≤ 2`). §28.10(iii) is bibliographic.

28.10.1–28.10.8 are proved by the kernel method: each kernel `K(z, t)` satisfies the PDE
`K_zz - 2q cos 2z K = K_tt - 2q cos 2t K`, so two integrations by parts show that the integral
`G(z)` solves Mathieu's equation with the eigenvalue of the integrand; parity and the value or
derivative at `z = 0` or `π/2` identify `G` as a multiple of `ce_n` or `se_n`, and the constant is a
quarter-period Fourier integral (`p1a2_quarter_*`) of §28.4.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Topology Real

namespace DLMF.Mathieu

/-- Differentiation under the integral sign for a jointly continuous kernel whose
`z`-derivative is jointly continuous. -/
lemma p1a2_hasDerivAt_integral {K K' : ℂ → ℝ → ℂ} {a b : ℝ}
    (hK : ∀ z t, HasDerivAt (fun z => K z t) (K' z t) z)
    (hcK : Continuous fun p : ℂ × ℝ => K p.1 p.2) (hcK' : Continuous fun p : ℂ × ℝ => K' p.1 p.2)
    (z₀ : ℂ) :
    HasDerivAt (fun z => ∫ t in a..b, K z t) (∫ t in a..b, K' z₀ t) z₀ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ 1).prod (isCompact_uIcc (a := a) (b := b))
    ).exists_bound_of_continuousOn hcK'.continuousOn
  have hKz : ∀ z, Continuous (K z) := fun z => hcK.comp (Continuous.prodMk_right z)
  have hK'z : ∀ z, Continuous (K' z) := fun z => hcK'.comp (Continuous.prodMk_right z)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => C) (Metric.closedBall_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hKz z).aestronglyMeasurable)
    ((hKz z₀).intervalIntegrable _ _) (hK'z z₀).aestronglyMeasurable ?_
    intervalIntegrable_const (Eventually.of_forall fun t _ z _ => hK z t)).2
  refine Eventually.of_forall fun t ht z hz => hC (z, t) ⟨hz, ?_⟩
  exact uIoc_subset_uIcc ht

/-- **Kernel criterion**: if the kernel `K(z, t)` satisfies
`(∂_z² - 2q cos 2z) K = (∂_t² - 2q cos 2t) K` and `f` solves Mathieu's equation on the real line,
with vanishing boundary form `[K_t f - K f']_α^β = 0`, then `z ↦ ∫_α^β K(z, t) f(t) dt` solves
Mathieu's equation. -/
theorem p1a2_isMathieuSolution_integral {a q : ℂ} {α β : ℝ} {K K1 K2 Kt Ktt : ℂ → ℝ → ℂ}
    {f f' : ℝ → ℂ}
    (hz1 : ∀ z t, HasDerivAt (fun z => K z t) (K1 z t) z)
    (hz2 : ∀ z t, HasDerivAt (fun z => K1 z t) (K2 z t) z)
    (ht1 : ∀ z t, HasDerivAt (fun t => K z t) (Kt z t) t)
    (ht2 : ∀ z t, HasDerivAt (fun t => Kt z t) (Ktt z t) t)
    (hc : Continuous fun p : ℂ × ℝ => K p.1 p.2) (hc1 : Continuous fun p : ℂ × ℝ => K1 p.1 p.2)
    (hc2 : Continuous fun p : ℂ × ℝ => K2 p.1 p.2)
    (hctt : ∀ z, Continuous (Ktt z))
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t : ℝ, HasDerivAt f' ((2 * q * Complex.cos (2 * (t : ℂ)) - a) * f t) t)
    (hpde : ∀ z t, K2 z t - 2 * q * Complex.cos (2 * z) * K z t =
      Ktt z t - 2 * q * Complex.cos (2 * (t : ℂ)) * K z t)
    (hbd : ∀ z, Kt z β * f β - K z β * f' β = Kt z α * f α - K z α * f' α) :
    IsMathieuSolution a q (fun z => ∫ t in α..β, K z t * f t) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun t => (hf' t).continuousAt
  have hG : ∀ z, HasDerivAt (fun z => ∫ t in α..β, K z t * f t) (∫ t in α..β, K1 z t * f t) z :=
    p1a2_hasDerivAt_integral (K := fun z t => K z t * f t) (K' := fun z t => K1 z t * f t)
      (fun z t => (hz1 z t).mul_const _) (hc.mul (hfc.comp continuous_snd))
      (hc1.mul (hfc.comp continuous_snd))
  have hG' : ∀ z, HasDerivAt (fun z => ∫ t in α..β, K1 z t * f t)
      (∫ t in α..β, K2 z t * f t) z :=
    p1a2_hasDerivAt_integral (K := fun z t => K1 z t * f t) (K' := fun z t => K2 z t * f t)
      (fun z t => (hz2 z t).mul_const _) (hc1.mul (hfc.comp continuous_snd))
      (hc2.mul (hfc.comp continuous_snd))
  have hd : deriv (fun z => ∫ t in α..β, K z t * f t) = fun z => ∫ t in α..β, K1 z t * f t :=
    funext fun z => (hG z).deriv
  refine ⟨fun z => (hG z).differentiableAt, fun z => ?_⟩
  rw [hd]
  convert hG' z using 1
  have hKz : Continuous (K z) := hc.comp (Continuous.prodMk_right z)
  have hcos : Continuous fun t : ℝ => Complex.cos (2 * (t : ℂ)) := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := α) (b := β)
    (f := fun t => Kt z t * f t - K z t * f' t)
    (f' := fun t => Ktt z t * f t - K z t * ((2 * q * Complex.cos (2 * t) - a) * f t))
    (fun t _ => by
      have := ((ht2 z t).mul (hf t)).sub ((ht1 z t).mul (hf' t))
      convert this using 1; ring)
    (by
      apply Continuous.intervalIntegrable
      exact ((hctt z).mul hfc).sub (hKz.mul ((continuous_const.mul hcos).sub continuous_const
        |>.mul hfc)))
  rw [hbd z, sub_self] at hint
  have hpt : ∀ t : ℝ, K2 z t * f t - (2 * q * Complex.cos (2 * z) - a) * (K z t * f t) =
      Ktt z t * f t - K z t * ((2 * q * Complex.cos (2 * t) - a) * f t) := by
    intro t
    have := hpde z t
    linear_combination f t * this
  have hc2z : Continuous (K2 z) := hc2.comp (Continuous.prodMk_right z)
  have e : ∫ t in α..β, (K2 z t * f t - (2 * q * Complex.cos (2 * z) - a) * (K z t * f t)) =
      (∫ t in α..β, K2 z t * f t) - (2 * q * Complex.cos (2 * z) - a) *
        ∫ t in α..β, K z t * f t := by
    rw [intervalIntegral.integral_sub (f := fun t => K2 z t * f t)
      (g := fun t => (2 * q * Complex.cos (2 * z) - a) * (K z t * f t))
      ((hc2z.mul hfc).intervalIntegrable _ _)
      (((hKz.mul hfc).const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  simp_rw [hpt] at e
  rw [hint] at e
  linear_combination e

/-- `ce_n` on the real line: derivative. -/
theorem p1a2_hasDerivAt_ce (n : ℕ) (q : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => mathieuCe n t q) (deriv (fun z => mathieuCe n z q) t) t :=
  ((isMathieuSolution_mathieuCe n q).differentiable t).hasDerivAt.comp_ofReal

/-- `ce_n` on the real line: second derivative (Mathieu's equation). -/
theorem p1a2_hasDerivAt_deriv_ce (n : ℕ) (q : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => deriv (fun z => mathieuCe n z q) t)
      ((2 * q * Complex.cos (2 * (t : ℂ)) - mathieuA n q) * mathieuCe n t q) t :=
  ((isMathieuSolution_mathieuCe n q).hasDerivAt_deriv t).comp_ofReal

/-- `se_n` on the real line: derivative. -/
theorem p1a2_hasDerivAt_se (n : ℕ) (q : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => mathieuSe n t q) (deriv (fun z => mathieuSe n z q) t) t :=
  ((isMathieuSolution_mathieuSe n q).differentiable t).hasDerivAt.comp_ofReal

/-- `se_n` on the real line: second derivative (Mathieu's equation). -/
theorem p1a2_hasDerivAt_deriv_se (n : ℕ) (q : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => deriv (fun z => mathieuSe n z q) t)
      ((2 * q * Complex.cos (2 * (t : ℂ)) - mathieuB n q) * mathieuSe n t q) t :=
  ((isMathieuSolution_mathieuSe n q).hasDerivAt_deriv t).comp_ofReal

/-- `ce_n'(0) = 0`. -/
lemma p1a2_deriv_ce_zero (n : ℕ) (q : ℝ) : deriv (fun z => mathieuCe n z q) 0 = 0 := by
  have h := (mathieuWI_spec (mathieuA n q) q)
  rw [show deriv (fun z => mathieuCe n z q) 0 =
      (mathieuCeZero n q : ℂ) * deriv (mathieuWI (mathieuA n q) q) 0 from
    ((h.1.differentiable 0).hasDerivAt.const_mul _).deriv, h.2.2, mul_zero]

/-- `se_n(0) = 0`. -/
lemma p1a2_se_zero (n : ℕ) (q : ℝ) : mathieuSe n 0 q = 0 := by
  simp [mathieuSe, (mathieuWII_spec (mathieuB n q) q).2.1]

/-- An even solution for `a = a_n(q)` is a multiple of `ce_n`. -/
theorem p1a2_eq_mul_ce {n : ℕ} {q : ℝ} {G : ℂ → ℂ}
    (hG : IsMathieuSolution (mathieuA n q) q G) (hev : ∀ z, G (-z) = G z) (z : ℂ) :
    G z = G 0 / mathieuCe n 0 q * mathieuCe n z q := by
  have hd0 : deriv G 0 = 0 := by
    have h := congrArg (fun f => deriv f 0) (funext hev)
    rw [deriv_comp_neg, neg_zero] at h
    linear_combination -h / 2
  have h := congrFun hG.eq_combination z
  rw [hd0, zero_mul, add_zero] at h
  rw [h, mathieuCe_zero, mathieuCe]
  have : (mathieuCeZero n q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne'
  field_simp

/-- An odd solution for `a = b_n(q)` is a multiple of `se_n`. -/
theorem p1a2_eq_mul_se {n : ℕ} {q : ℝ} {G : ℂ → ℂ}
    (hG : IsMathieuSolution (mathieuB n q) q G) (hodd : ∀ z, G (-z) = -G z) (z : ℂ) :
    G z = deriv G 0 / deriv (fun z => mathieuSe n z q) 0 * mathieuSe n z q := by
  have h0 : G 0 = 0 := by
    have := hodd 0
    rw [neg_zero] at this
    linear_combination this / 2
  have h := congrFun hG.eq_combination z
  rw [h0, zero_mul, zero_add] at h
  rw [h, deriv_mathieuSe_zero, mathieuSe]
  have : (mathieuSeDerivZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos n q).ne'
  field_simp

/-- For an even `π`-periodic `g`, `∫₀^{2π} g = 4 ∫₀^{π/2} g`. -/
theorem p1a2_integral_quarter {g : ℝ → ℂ} (hg : Continuous g) (hper : ∀ x, g (x + π) = g x)
    (hev : ∀ x, g (-x) = g x) :
    ∫ x in (0 : ℝ)..2 * π, g x = 4 * ∫ x in (0 : ℝ)..π / 2, g x := by
  have hi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hi _ _) (hi _ _)]
  have h1 := intervalIntegral.integral_comp_add_right (a := 0) (b := π) g π
  rw [zero_add, show π + π = 2 * π by ring] at h1
  rw [← h1]
  simp_rw [hper]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := π / 2) (c := π) (hi _ _)
    (hi _ _)]
  have h2 : ∫ x in (π / 2)..π, g x = ∫ x in (0 : ℝ)..π / 2, g x := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2) g π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at this
    rw [← this]
    congr 1; funext x
    rw [show π - x = -x + π by ring, hper, hev]
  rw [h2]; ring

/-- `ce_{2n}'(π/2) = 0` (DLMF 28.2.21). -/
theorem p1a2_deriv_ce_even_half_pi (n : ℕ) (q : ℝ) :
    deriv (fun z => mathieuCe (2 * n) z q) ((π / 2 : ℝ) : ℂ) = 0 := by
  have h := mathieuWI_spec (mathieuA (2 * n) q) q
  rw [show deriv (fun z => mathieuCe (2 * n) z q) ((π / 2 : ℝ) : ℂ) =
      (mathieuCeZero (2 * n) q : ℂ) * deriv (mathieuWI (mathieuA (2 * n) q) q) ((π / 2 : ℝ) : ℂ)
      from ((h.1.differentiable _).hasDerivAt.const_mul _).deriv]
  push_cast
  rw [deriv_mathieuWI_half_pi_mathieuA_even, mul_zero]

/-- `t ↦ cos t` as a complex-valued function of real `t`. -/
lemma p1a2_hasDerivAt_rcos (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((Real.cos t : ℝ) : ℂ)) (-((Real.sin t : ℝ) : ℂ)) t := by
  simpa using (Real.hasDerivAt_cos t).ofReal_comp

/-- `t ↦ sin t` as a complex-valued function of real `t`. -/
lemma p1a2_hasDerivAt_rsin (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((Real.sin t : ℝ) : ℂ)) ((Real.cos t : ℝ) : ℂ) t :=
  (Real.hasDerivAt_sin t).ofReal_comp

/-- First and second derivatives of `x ↦ P(x) Φ(u(x))`. -/
lemma p1a2_hasDerivAt_mul_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {P P1 P2 u u1 u2 : 𝕜 → ℂ} {Φ Φ1 Φ2 : ℂ → ℂ} {x : 𝕜}
    (hP : HasDerivAt P (P1 x) x) (hP1 : HasDerivAt P1 (P2 x) x)
    (hu : HasDerivAt u (u1 x) x) (hu1 : HasDerivAt u1 (u2 x) x)
    (hΦ : ∀ w, HasDerivAt Φ (Φ1 w) w) (hΦ1 : ∀ w, HasDerivAt Φ1 (Φ2 w) w) :
    HasDerivAt (fun x => P x * Φ (u x)) (P1 x * Φ (u x) + P x * (Φ1 (u x) * u1 x)) x ∧
    HasDerivAt (fun x => P1 x * Φ (u x) + P x * (Φ1 (u x) * u1 x))
      (P2 x * Φ (u x) + P1 x * (Φ1 (u x) * u1 x) +
        (P1 x * (Φ1 (u x) * u1 x) + P x * (Φ2 (u x) * u1 x * u1 x + Φ1 (u x) * u2 x))) x := by
  have h0 : HasDerivAt (fun x => Φ (u x)) (Φ1 (u x) * u1 x) x := (hΦ (u x)).comp x hu
  have h1 : HasDerivAt (fun x => Φ1 (u x)) (Φ2 (u x) * u1 x) x := (hΦ1 (u x)).comp x hu
  refine ⟨hP.mul h0, ?_⟩
  convert (hP1.mul h0).add (hP.mul (h1.mul hu1)) using 1

/-- **Kernel criterion, product form** `K(z, t) = P(z, t) Φ(u(z, t))`. -/
lemma p1a2_isMathieuSolution_kernel {a q : ℂ} {α β : ℝ} {f f' : ℝ → ℂ}
    {P Pz Pzz Pt Ptt u uz uzz ut utt : ℂ → ℝ → ℂ} {Φ Φ1 Φ2 : ℂ → ℂ}
    (hPz : ∀ z t, HasDerivAt (fun z => P z t) (Pz z t) z)
    (hPzz : ∀ z t, HasDerivAt (fun z => Pz z t) (Pzz z t) z)
    (hPt : ∀ z t, HasDerivAt (fun t => P z t) (Pt z t) t)
    (hPtt : ∀ z t, HasDerivAt (fun t => Pt z t) (Ptt z t) t)
    (huz : ∀ z t, HasDerivAt (fun z => u z t) (uz z t) z)
    (huzz : ∀ z t, HasDerivAt (fun z => uz z t) (uzz z t) z)
    (hut : ∀ z t, HasDerivAt (fun t => u z t) (ut z t) t)
    (hutt : ∀ z t, HasDerivAt (fun t => ut z t) (utt z t) t)
    (hΦ : ∀ w, HasDerivAt Φ (Φ1 w) w) (hΦ1 : ∀ w, HasDerivAt Φ1 (Φ2 w) w)
    (hΦ2 : Continuous Φ2)
    (hcP : Continuous fun p : ℂ × ℝ => P p.1 p.2) (hcPz : Continuous fun p : ℂ × ℝ => Pz p.1 p.2)
    (hcPzz : Continuous fun p : ℂ × ℝ => Pzz p.1 p.2)
    (hcu : Continuous fun p : ℂ × ℝ => u p.1 p.2) (hcuz : Continuous fun p : ℂ × ℝ => uz p.1 p.2)
    (hcuzz : Continuous fun p : ℂ × ℝ => uzz p.1 p.2)
    (hcPt : ∀ z, Continuous (Pt z)) (hcPtt : ∀ z, Continuous (Ptt z))
    (hcut : ∀ z, Continuous (ut z)) (hcutt : ∀ z, Continuous (utt z))
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t : ℝ, HasDerivAt f' ((2 * q * Complex.cos (2 * (t : ℂ)) - a) * f t) t)
    (hpde : ∀ z t, (Pzz z t * Φ (u z t) + Pz z t * (Φ1 (u z t) * uz z t) +
        (Pz z t * (Φ1 (u z t) * uz z t) + P z t * (Φ2 (u z t) * uz z t * uz z t +
          Φ1 (u z t) * uzz z t))) - 2 * q * Complex.cos (2 * z) * (P z t * Φ (u z t)) =
      (Ptt z t * Φ (u z t) + Pt z t * (Φ1 (u z t) * ut z t) +
        (Pt z t * (Φ1 (u z t) * ut z t) + P z t * (Φ2 (u z t) * ut z t * ut z t +
          Φ1 (u z t) * utt z t))) - 2 * q * Complex.cos (2 * (t : ℂ)) * (P z t * Φ (u z t)))
    (hbd : ∀ z, (Pt z β * Φ (u z β) + P z β * (Φ1 (u z β) * ut z β)) * f β -
        P z β * Φ (u z β) * f' β =
      (Pt z α * Φ (u z α) + P z α * (Φ1 (u z α) * ut z α)) * f α -
        P z α * Φ (u z α) * f' α) :
    IsMathieuSolution a q (fun z => ∫ t in α..β, P z t * Φ (u z t) * f t) ∧
      ∀ z, HasDerivAt (fun z => ∫ t in α..β, P z t * Φ (u z t) * f t)
        (∫ t in α..β, (Pz z t * Φ (u z t) + P z t * (Φ1 (u z t) * uz z t)) * f t) z := by
  have hcΦ : Continuous Φ := continuous_iff_continuousAt.2 fun w => (hΦ w).continuousAt
  have hcΦ1 : Continuous Φ1 := continuous_iff_continuousAt.2 fun w => (hΦ1 w).continuousAt
  have hPtc : ∀ z, Continuous (P z) := fun z =>
    continuous_iff_continuousAt.2 fun t => (hPt z t).continuousAt
  have hutc : ∀ z, Continuous (u z) := fun z =>
    continuous_iff_continuousAt.2 fun t => (hut z t).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  refine ⟨?_, fun z => p1a2_hasDerivAt_integral (K := fun z t => P z t * Φ (u z t) * f t)
    (fun z t => (((p1a2_hasDerivAt_mul_comp (P := fun z => P z t) (P1 := fun z => Pz z t)
      (P2 := fun z => Pzz z t) (u := fun z => u z t) (u1 := fun z => uz z t)
      (u2 := fun z => uzz z t) (hPz z t) (hPzz z t) (huz z t) (huzz z t) hΦ hΦ1).1).mul_const
        (f t)))
    ((hcP.mul (hcΦ.comp hcu)).mul (hfc.comp continuous_snd))
    (((hcPz.mul (hcΦ.comp hcu)).add (hcP.mul ((hcΦ1.comp hcu).mul hcuz))).mul
      (hfc.comp continuous_snd)) z⟩
  refine p1a2_isMathieuSolution_integral
    (fun z t => (p1a2_hasDerivAt_mul_comp (P := fun z => P z t) (P1 := fun z => Pz z t)
      (P2 := fun z => Pzz z t) (u := fun z => u z t) (u1 := fun z => uz z t)
      (u2 := fun z => uzz z t) (hPz z t) (hPzz z t) (huz z t) (huzz z t) hΦ hΦ1).1)
    (fun z t => (p1a2_hasDerivAt_mul_comp (P := fun z => P z t) (P1 := fun z => Pz z t)
      (P2 := fun z => Pzz z t) (u := fun z => u z t) (u1 := fun z => uz z t)
      (u2 := fun z => uzz z t) (hPz z t) (hPzz z t) (huz z t) (huzz z t) hΦ hΦ1).2)
    (fun z t => (p1a2_hasDerivAt_mul_comp (hPt z t) (hPtt z t) (hut z t) (hutt z t) hΦ hΦ1).1)
    (fun z t => (p1a2_hasDerivAt_mul_comp (hPt z t) (hPtt z t) (hut z t) (hutt z t) hΦ hΦ1).2)
    (hcP.mul (hcΦ.comp hcu))
    ((hcPz.mul (hcΦ.comp hcu)).add (hcP.mul ((hcΦ1.comp hcu).mul hcuz)))
    (((hcPzz.mul (hcΦ.comp hcu)).add (hcPz.mul ((hcΦ1.comp hcu).mul hcuz))).add
      ((hcPz.mul ((hcΦ1.comp hcu).mul hcuz)).add (hcP.mul ((((hΦ2.comp hcu).mul hcuz).mul
        hcuz).add ((hcΦ1.comp hcu).mul hcuzz)))))
    (fun z => (((hcPtt z).mul (hcΦ.comp (hutc z))).add ((hcPt z).mul ((hcΦ1.comp (hutc z)).mul
      (hcut z)))).add (((hcPt z).mul ((hcΦ1.comp (hutc z)).mul (hcut z))).add ((hPtc z).mul
        ((((hΦ2.comp (hutc z)).mul (hcut z)).mul (hcut z)).add
          ((hcΦ1.comp (hutc z)).mul (hcutt z))))))
    hf hf' hpde hbd

/-- A solution vanishing together with its derivative at a point is zero. -/
lemma p1a2_eq_zero_of_initial {a q : ℂ} {w : ℂ → ℂ} (hw : IsMathieuSolution a q w) {z₀ : ℂ}
    (h0 : w z₀ = 0) (h1 : deriv w z₀ = 0) : w = fun _ => 0 := by
  have := hw.eq_of_initial (hw.const_mul 0) (z₀ := z₀) (by simp [h0])
    (by rw [show deriv (fun z => (0 : ℂ) * w z) z₀ = 0 by simp, h1])
  rw [this]; funext z; simp

/-- `ce_n` and `ce_n'` do not vanish simultaneously. -/
theorem p1a2_ce_or_deriv_ne_zero (n : ℕ) (q : ℝ) (z₀ : ℂ) (h0 : mathieuCe n z₀ q = 0)
    (h1 : deriv (fun z => mathieuCe n z q) z₀ = 0) : False := by
  have := congrFun (p1a2_eq_zero_of_initial (isMathieuSolution_mathieuCe n q) h0 h1) 0
  rw [mathieuCe_zero] at this
  exact (mathieuCeZero_pos n q).ne' (by exact_mod_cast this)

/-- `se_n` and `se_n'` do not vanish simultaneously. -/
theorem p1a2_se_or_deriv_ne_zero (n : ℕ) (q : ℝ) (z₀ : ℂ) (h0 : mathieuSe n z₀ q = 0)
    (h1 : deriv (fun z => mathieuSe n z q) z₀ = 0) : False := by
  have := p1a2_eq_zero_of_initial (isMathieuSolution_mathieuSe n q) h0 h1
  have h2 := deriv_mathieuSe_zero n q
  rw [this] at h2
  simp only [deriv_const] at h2
  exact (mathieuSeDerivZero_pos n q).ne' (by exact_mod_cast h2.symm)

/-- Identification of the constant for an even solution, by a value. -/
lemma p1a2_finish_val_ce {n : ℕ} {q : ℝ} {G : ℂ → ℂ}
    (hG : IsMathieuSolution (mathieuA n q) q G) (hev : ∀ z, G (-z) = G z) {z₀ A : ℂ}
    (hne : mathieuCe n z₀ q ≠ 0) (hval : 2 / π * G z₀ = A) (z : ℂ) :
    2 / π * G z = A / mathieuCe n z₀ q * mathieuCe n z q := by
  have hrep := p1a2_eq_mul_ce hG hev
  rw [← hval, hrep z, hrep z₀]
  field_simp

/-- Identification of the constant for an even solution, by a derivative. -/
lemma p1a2_finish_der_ce {n : ℕ} {q : ℝ} {G : ℂ → ℂ}
    (hG : IsMathieuSolution (mathieuA n q) q G) (hev : ∀ z, G (-z) = G z) {z₀ A : ℂ}
    (hne : deriv (fun z => mathieuCe n z q) z₀ ≠ 0) (hval : 2 / π * deriv G z₀ = A) (z : ℂ) :
    2 / π * G z = A / deriv (fun z => mathieuCe n z q) z₀ * mathieuCe n z q := by
  obtain ⟨c, hc⟩ : ∃ c, G = fun z => c * mathieuCe n z q := ⟨_, funext (p1a2_eq_mul_ce hG hev)⟩
  have hd : deriv G z₀ = c * deriv (fun z => mathieuCe n z q) z₀ := by
    rw [hc]
    exact (((isMathieuSolution_mathieuCe n q).differentiable z₀).hasDerivAt.const_mul _).deriv
  rw [← hval, hd, hc]
  field_simp

/-- Identification of the constant for an odd solution, by a value. -/
lemma p1a2_finish_val_se {n : ℕ} {q : ℝ} {G : ℂ → ℂ}
    (hG : IsMathieuSolution (mathieuB n q) q G) (hodd : ∀ z, G (-z) = -G z) {z₀ A : ℂ}
    (hne : mathieuSe n z₀ q ≠ 0) (hval : 2 / π * G z₀ = A) (z : ℂ) :
    2 / π * G z = A / mathieuSe n z₀ q * mathieuSe n z q := by
  have hrep := p1a2_eq_mul_se hG hodd
  have : deriv (fun z => mathieuSe n z q) 0 ≠ 0 := by
    rw [deriv_mathieuSe_zero]
    exact Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos n q).ne'
  rw [← hval, hrep z, hrep z₀]
  field_simp

/-- Identification of the constant for an odd solution, by a derivative. -/
lemma p1a2_finish_der_se {n : ℕ} {q : ℝ} {G : ℂ → ℂ}
    (hG : IsMathieuSolution (mathieuB n q) q G) (hodd : ∀ z, G (-z) = -G z) {z₀ A : ℂ}
    (hne : deriv (fun z => mathieuSe n z q) z₀ ≠ 0) (hval : 2 / π * deriv G z₀ = A) (z : ℂ) :
    2 / π * G z = A / deriv (fun z => mathieuSe n z q) z₀ * mathieuSe n z q := by
  obtain ⟨c, hc⟩ : ∃ c, G = fun z => c * mathieuSe n z q := ⟨_, funext (p1a2_eq_mul_se hG hodd)⟩
  have hd : deriv G z₀ = c * deriv (fun z => mathieuSe n z q) z₀ := by
    rw [hc]
    exact (((isMathieuSolution_mathieuSe n q).differentiable z₀).hasDerivAt.const_mul _).deriv
  rw [← hval, hd, hc]
  field_simp

/-- `∫₀^{π/2} ce_{2n} = (π/2) A^{2n}_0`. -/
theorem p1a2_quarter_A0 (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π / 2, mathieuCe (2 * n) t q = π / 2 * mathieuFourierA (2 * n) 0 q := by
  rw [mathieuFourierA]
  simp only [↓reduceIte, Nat.cast_zero, zero_mul, Complex.cos_zero, mul_one]
  rw [p1a2_integral_quarter (g := fun t : ℝ => mathieuCe (2 * n) t q)]
  · have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring
  · exact (isMathieuSolution_mathieuCe _ _).differentiable.continuous.comp
      Complex.continuous_ofReal
  · intro x; push_cast; exact mathieuCe_even_add_pi n x _
  · intro x; push_cast; exact mathieuCe_neg _ x _

/-- `∫₀^{π/2} cos t ce_{2n+1}(t) dt = (π/4) A^{2n+1}_1`. -/
theorem p1a2_quarter_A1 (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π / 2, ((Real.cos t : ℝ) : ℂ) * mathieuCe (2 * n + 1) t q =
      π / 4 * mathieuFourierA (2 * n + 1) 1 q := by
  rw [mathieuFourierA]
  simp only [one_ne_zero, ↓reduceIte, Nat.cast_one, one_mul]
  rw [p1a2_integral_quarter (g := fun t : ℝ => mathieuCe (2 * n + 1) t q * Complex.cos t)]
  · have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Complex.ofReal_cos, mul_comm (Complex.cos _)]
    field_simp
  · have := (isMathieuSolution_mathieuCe (2 * n + 1) q).differentiable.continuous; fun_prop
  · intro x; push_cast; rw [mathieuCe_odd_add_pi, Complex.cos_add_pi]; ring
  · intro x; push_cast; rw [mathieuCe_neg, Complex.cos_neg]

/-- `∫₀^{π/2} sin t se_{2n+1}(t) dt = (π/4) B^{2n+1}_1`. -/
theorem p1a2_quarter_B1 (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π / 2, ((Real.sin t : ℝ) : ℂ) * mathieuSe (2 * n + 1) t q =
      π / 4 * mathieuFourierB (2 * n + 1) 1 q := by
  rw [mathieuFourierB]
  simp only [Nat.cast_one, one_mul]
  rw [p1a2_integral_quarter (g := fun t : ℝ => mathieuSe (2 * n + 1) t q * Complex.sin t)]
  · have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Complex.ofReal_sin, mul_comm (Complex.sin _)]
    field_simp
  · have := (isMathieuSolution_mathieuSe (2 * n + 1) q).differentiable.continuous; fun_prop
  · intro x; push_cast; rw [mathieuSe_odd_add_pi, Complex.sin_add_pi]; ring
  · intro x; push_cast; rw [mathieuSe_neg, Complex.sin_neg]; ring

/-- `∫₀^{π/2} sin t cos t se_{2n+2}(t) dt = (π/8) B^{2n+2}_2`. -/
theorem p1a2_quarter_B2 (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π / 2, ((Real.sin t : ℝ) : ℂ) * ((Real.cos t : ℝ) : ℂ) *
        mathieuSe (2 * n + 2) t q = π / 8 * mathieuFourierB (2 * n + 2) 2 q := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : ∀ x : ℝ, mathieuSe (2 * n + 2) x q * Complex.sin (((2 : ℕ) : ℂ) * x) =
      2 * (mathieuSe (2 * n + 2) x q * (Complex.sin x * Complex.cos x)) := by
    intro x; push_cast; rw [Complex.sin_two_mul]; ring
  rw [mathieuFourierB]
  simp_rw [e, intervalIntegral.integral_const_mul]
  rw [p1a2_integral_quarter (g := fun t : ℝ => mathieuSe (2 * n + 2) t q *
    (Complex.sin t * Complex.cos t))]
  · simp only [Complex.ofReal_sin, Complex.ofReal_cos]
    rw [show (∫ t in (0 : ℝ)..π / 2, Complex.sin t * Complex.cos t * mathieuSe (2 * n + 2) t q)
      = ∫ t in (0 : ℝ)..π / 2, mathieuSe (2 * n + 2) t q * (Complex.sin t * Complex.cos t) by
        congr 1; funext t; ring]
    field_simp; ring
  · have := (isMathieuSolution_mathieuSe (2 * n + 2) q).differentiable.continuous; fun_prop
  · intro x; push_cast; rw [mathieuSe_even_add_pi, Complex.sin_add_pi, Complex.cos_add_pi]; ring
  · intro x; push_cast; rw [mathieuSe_neg, Complex.sin_neg, Complex.cos_neg]; ring

/-- **DLMF 28.10.1**: `(2/π) ∫₀^{π/2} cos(2h cos z cos t) ce_{2n}(t, h²) dt
= A^{2n}_0(h²)/ce_{2n}(π/2, h²) · ce_{2n}(z, h²)`. -/
@[dlmf 28.10.E1]
theorem integral_cos_mathieuCe_even (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2,
        Complex.cos (2 * h * Complex.cos z * Real.cos t) * mathieuCe (2 * n) t (h ^ 2) =
      mathieuFourierA (2 * n) 0 (h ^ 2) / mathieuCe (2 * n) (π / 2) (h ^ 2) *
        mathieuCe (2 * n) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  let u : ℂ → ℝ → ℂ := fun z t => 2 * H * Complex.cos z * Real.cos t
  have hG := p1a2_isMathieuSolution_integral (α := 0) (β := π / 2)
    (K := fun z t => Complex.cos (u z t))
    (K1 := fun z t => 2 * H * Complex.sin z * Real.cos t * Complex.sin (u z t))
    (K2 := fun z t => 2 * H * Complex.cos z * Real.cos t * Complex.sin (u z t) -
      4 * H ^ 2 * Complex.sin z ^ 2 * (Real.cos t : ℂ) ^ 2 * Complex.cos (u z t))
    (Kt := fun z t => 2 * H * Complex.cos z * Real.sin t * Complex.sin (u z t))
    (Ktt := fun z t => 2 * H * Complex.cos z * Real.cos t * Complex.sin (u z t) -
      4 * H ^ 2 * Complex.cos z ^ 2 * (Real.sin t : ℂ) ^ 2 * Complex.cos (u z t))
    (f := fun t => mathieuCe (2 * n) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuCe (2 * n) z (h ^ 2)) t)
    (a := mathieuA (2 * n) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    (fun z t => by
      have hu : HasDerivAt (fun z => u z t) (2 * H * (-Complex.sin z) * Real.cos t) z :=
        (((Complex.hasDerivAt_cos z).const_mul (2 * H)).mul_const _)
      have h2 : HasDerivAt (fun z => Complex.cos (u z t))
          (-Complex.sin (u z t) * (2 * H * (-Complex.sin z) * Real.cos t)) z :=
        (Complex.hasDerivAt_cos _).comp z hu
      convert h2 using 1; ring)
    (fun z t => by
      have hu : HasDerivAt (fun z => u z t) (2 * H * (-Complex.sin z) * Real.cos t) z :=
        (((Complex.hasDerivAt_cos z).const_mul (2 * H)).mul_const _)
      have h2 : HasDerivAt (fun z => Complex.sin (u z t))
          (Complex.cos (u z t) * (2 * H * (-Complex.sin z) * Real.cos t)) z :=
        (Complex.hasDerivAt_sin _).comp z hu
      have h1 := (((Complex.hasDerivAt_sin z).const_mul (2 * H)).mul_const
        ((Real.cos t : ℝ) : ℂ)).mul h2
      convert h1 using 1; ring)
    (fun z t => by
      have hu : HasDerivAt (fun t => u z t) (2 * H * Complex.cos z * -((Real.sin t : ℝ) : ℂ)) t :=
        (p1a2_hasDerivAt_rcos t).const_mul _
      have h2 : HasDerivAt (fun t => Complex.cos (u z t))
          (-Complex.sin (u z t) * (2 * H * Complex.cos z * -((Real.sin t : ℝ) : ℂ))) t :=
        (Complex.hasDerivAt_cos _).comp t hu
      convert h2 using 1; ring)
    (fun z t => by
      have hu : HasDerivAt (fun t => u z t) (2 * H * Complex.cos z * -((Real.sin t : ℝ) : ℂ)) t :=
        (p1a2_hasDerivAt_rcos t).const_mul _
      have h2 : HasDerivAt (fun t => Complex.sin (u z t))
          (Complex.cos (u z t) * (2 * H * Complex.cos z * -((Real.sin t : ℝ) : ℂ))) t :=
        (Complex.hasDerivAt_sin _).comp t hu
      have h1 := ((p1a2_hasDerivAt_rsin t).const_mul (2 * H * Complex.cos z)).mul h2
      convert h1 using 1; ring)
    (by simp only [u]; fun_prop) (by simp only [u]; fun_prop) (by simp only [u]; fun_prop)
    (fun z => by simp only [u]; fun_prop)
    (p1a2_hasDerivAt_ce _ _) (p1a2_hasDerivAt_deriv_ce _ _)
    (fun z t => by
      simp only [u]
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * Complex.cos (2 * H * Complex.cos z * Real.cos t) *
        (Real.cos t : ℂ) ^ 2) * e1 + (4 * H ^ 2 * Complex.cos (2 * H * Complex.cos z * Real.cos t) *
        Complex.cos z ^ 2) * e2)
    (fun z => by
      simp only [u, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero,
        Complex.ofReal_one, mul_zero, zero_mul, Complex.sin_zero, p1a2_deriv_ce_zero]
      rw [p1a2_deriv_ce_even_half_pi]; ring)
  set G := fun z => ∫ t in (0 : ℝ)..π / 2, Complex.cos (u z t) * mathieuCe (2 * n) t (h ^ 2)
    with hGdef
  have hev : ∀ z, G (-z) = G z := fun z => by simp only [hGdef, u, Complex.cos_neg]
  have hrep := p1a2_eq_mul_ce hG hev
  have hhalf : G (π / 2) = π / 2 * mathieuFourierA (2 * n) 0 (h ^ 2) := by
    simp only [hGdef, u, Complex.cos_pi_div_two, mul_zero, zero_mul, Complex.cos_zero, one_mul]
    rw [mathieuFourierA]
    simp only [↓reduceIte, Nat.cast_zero, zero_mul, Complex.cos_zero, mul_one]
    rw [p1a2_integral_quarter (g := fun t : ℝ => mathieuCe (2 * n) t (h ^ 2))]
    · have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp; ring
    · exact (isMathieuSolution_mathieuCe _ _).differentiable.continuous.comp
        Complex.continuous_ofReal
    · intro x; push_cast; exact mathieuCe_even_add_pi n x _
    · intro x; push_cast; exact mathieuCe_neg _ x _
  have hne : mathieuCe (2 * n) (π / 2) (h ^ 2) ≠ 0 := by
    intro h0
    have hsol := isMathieuSolution_mathieuCe (2 * n) (h ^ 2)
    have := hsol.eq_of_initial (hsol.const_mul 0) (z₀ := π / 2) (by simp [h0]) (by
      rw [show deriv (fun z => (0 : ℂ) * mathieuCe (2 * n) z (h ^ 2)) (π / 2) = 0 by simp]
      have := p1a2_deriv_ce_even_half_pi n (h ^ 2)
      push_cast at this; exact this)
    have h00 := congrFun this 0
    simp only [zero_mul, mathieuCe_zero] at h00
    exact (mathieuCeZero_pos (2 * n) (h ^ 2)).ne' (by exact_mod_cast h00)
  have e1 := hrep z
  have e2 := hrep (π / 2)
  rw [hhalf] at e2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hA : mathieuFourierA (2 * n) 0 (h ^ 2) = 2 / π * (G 0 / mathieuCe (2 * n) 0 (h ^ 2) *
      mathieuCe (2 * n) (π / 2) (h ^ 2)) := by
    rw [← e2]; field_simp
  change 2 / π * G z = _
  rw [e1, hA]
  field_simp

/-- Constant factor: derivative facts. -/
lemma p1a2_hd_one_z : ∀ (z : ℂ) (_t : ℝ), HasDerivAt (fun _ : ℂ => (1 : ℂ)) 0 z :=
  fun _ _ => hasDerivAt_const _ _

/-- Constant factor in `t`. -/
lemma p1a2_hd_one_t : ∀ (_z : ℂ) (t : ℝ), HasDerivAt (fun _ : ℝ => (1 : ℂ)) 0 t :=
  fun _ _ => hasDerivAt_const _ _

/-- Zero factor in `z`. -/
lemma p1a2_hd_zero_z : ∀ (z : ℂ) (_t : ℝ), HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 z :=
  fun _ _ => hasDerivAt_const _ _

/-- Zero factor in `t`. -/
lemma p1a2_hd_zero_t : ∀ (_z : ℂ) (t : ℝ), HasDerivAt (fun _ : ℝ => (0 : ℂ)) 0 t :=
  fun _ _ => hasDerivAt_const _ _

/-- **DLMF 28.10.2**: `(2/π) ∫₀^{π/2} cosh(2h sin z sin t) ce_{2n}(t, h²) dt
= A^{2n}_0(h²)/ce_{2n}(0, h²) · ce_{2n}(z, h²)`. -/
@[dlmf 28.10.E2]
theorem integral_cosh_mathieuCe_even (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2,
        Complex.cosh (2 * h * Complex.sin z * Real.sin t) * mathieuCe (2 * n) t (h ^ 2) =
      mathieuFourierA (2 * n) 0 (h ^ 2) / mathieuCe (2 * n) 0 (h ^ 2) *
        mathieuCe (2 * n) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  obtain ⟨hG, -⟩ := p1a2_isMathieuSolution_kernel (α := 0) (β := π / 2)
    (P := fun _ _ => 1) (Pz := fun _ _ => 0) (Pzz := fun _ _ => 0) (Pt := fun _ _ => 0)
    (Ptt := fun _ _ => 0)
    (u := fun z t => 2 * H * Complex.sin z * Real.sin t)
    (uz := fun z t => 2 * H * Complex.cos z * Real.sin t)
    (uzz := fun z t => 2 * H * -Complex.sin z * Real.sin t)
    (ut := fun z t => 2 * H * Complex.sin z * Real.cos t)
    (utt := fun z t => 2 * H * Complex.sin z * -((Real.sin t : ℝ) : ℂ))
    (Φ := Complex.cosh) (Φ1 := Complex.sinh) (Φ2 := Complex.cosh)
    (f := fun t => mathieuCe (2 * n) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuCe (2 * n) z (h ^ 2)) t)
    (a := mathieuA (2 * n) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    p1a2_hd_one_z p1a2_hd_zero_z p1a2_hd_one_t p1a2_hd_zero_t
    (fun z t => ((Complex.hasDerivAt_sin z).const_mul _).mul_const _)
    (fun z t => ((Complex.hasDerivAt_cos z).const_mul _).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rsin t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    Complex.hasDerivAt_cosh Complex.hasDerivAt_sinh Complex.continuous_cosh
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop)
    (p1a2_hasDerivAt_ce _ _) (p1a2_hasDerivAt_deriv_ce _ _)
    (fun z t => by
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * (Real.cos t : ℂ) ^ 2 *
        Complex.cosh (2 * H * Complex.sin z * Real.sin t)) * e1 +
        (4 * H ^ 2 * Complex.cos z ^ 2 * Complex.cosh (2 * H * Complex.sin z * Real.sin t)) * e2)
    (fun z => by
      simp only [Real.sin_zero, Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero,
        Complex.sinh_zero, zero_mul, add_zero, p1a2_deriv_ce_even_half_pi, Complex.ofReal_zero,
        p1a2_deriv_ce_zero])
  have hev : ∀ z, (fun z => ∫ t in (0 : ℝ)..π / 2, 1 * Complex.cosh (2 * H * Complex.sin z *
      Real.sin t) * mathieuCe (2 * n) t (h ^ 2)) (-z) = (fun z => ∫ t in (0 : ℝ)..π / 2,
      1 * Complex.cosh (2 * H * Complex.sin z * Real.sin t) * mathieuCe (2 * n) t (h ^ 2)) z := by
    intro z
    simp only [Complex.sin_neg]
    congr 1; funext t
    rw [show 2 * H * -Complex.sin z * ((Real.sin t : ℝ) : ℂ) =
      -(2 * H * Complex.sin z * Real.sin t) by ring, Complex.cosh_neg]
  have hne : mathieuCe (2 * n) 0 (h ^ 2) ≠ 0 := by
    rw [mathieuCe_zero]; exact Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos _ _).ne'
  have := p1a2_finish_val_ce hG hev hne (A := mathieuFourierA (2 * n) 0 (h ^ 2)) (by
    simp only [Complex.sin_zero, mul_zero, zero_mul, Complex.cosh_zero, one_mul]
    rw [p1a2_quarter_A0]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp) z
  simpa only [one_mul] using this

/-- `ce_{2n+1}(π/2) = 0` (DLMF 28.2.21). -/
theorem p1a2_ce_odd_half_pi (n : ℕ) (q : ℝ) :
    mathieuCe (2 * n + 1) ((π / 2 : ℝ) : ℂ) q = 0 := by
  rw [mathieuCe]; push_cast; rw [mathieuWI_half_pi_mathieuA_odd, mul_zero]

/-- `se_{2n+2}(π/2) = 0` (DLMF 28.2.22). -/
theorem p1a2_se_even_half_pi (n : ℕ) (q : ℝ) :
    mathieuSe (2 * n + 2) ((π / 2 : ℝ) : ℂ) q = 0 := by
  rw [mathieuSe]; push_cast; rw [mathieuWII_half_pi_mathieuB_even, mul_zero]

/-- `se_{2n+1}'(π/2) = 0` (DLMF 28.2.22). -/
theorem p1a2_deriv_se_odd_half_pi (n : ℕ) (q : ℝ) :
    deriv (fun z => mathieuSe (2 * n + 1) z q) ((π / 2 : ℝ) : ℂ) = 0 := by
  have h := mathieuWII_spec (mathieuB (2 * n + 1) q) q
  rw [show deriv (fun z => mathieuSe (2 * n + 1) z q) ((π / 2 : ℝ) : ℂ) =
      (mathieuSeDerivZero (2 * n + 1) q : ℂ) *
        deriv (mathieuWII (mathieuB (2 * n + 1) q) q) ((π / 2 : ℝ) : ℂ)
      from ((h.1.differentiable _).hasDerivAt.const_mul _).deriv]
  push_cast
  rw [deriv_mathieuWII_half_pi_mathieuB_odd, mul_zero]

/-- **DLMF 28.10.3**: `(2/π) ∫₀^{π/2} sin(2h cos z cos t) ce_{2n+1}(t, h²) dt
= -h A^{2n+1}_1(h²)/ce'_{2n+1}(π/2, h²) · ce_{2n+1}(z, h²)`. -/
@[dlmf 28.10.E3]
theorem integral_sin_mathieuCe_odd (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2,
        Complex.sin (2 * h * Complex.cos z * Real.cos t) * mathieuCe (2 * n + 1) t (h ^ 2) =
      -(h * mathieuFourierA (2 * n + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuCe (2 * n + 1) w (h ^ 2)) (π / 2)) *
        mathieuCe (2 * n + 1) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  obtain ⟨hG, hder⟩ := p1a2_isMathieuSolution_kernel (α := 0) (β := π / 2)
    (P := fun _ _ => 1) (Pz := fun _ _ => 0) (Pzz := fun _ _ => 0) (Pt := fun _ _ => 0)
    (Ptt := fun _ _ => 0)
    (u := fun z t => 2 * H * Complex.cos z * Real.cos t)
    (uz := fun z t => 2 * H * -Complex.sin z * Real.cos t)
    (uzz := fun z t => 2 * H * -Complex.cos z * Real.cos t)
    (ut := fun z t => 2 * H * Complex.cos z * -((Real.sin t : ℝ) : ℂ))
    (utt := fun z t => 2 * H * Complex.cos z * -((Real.cos t : ℝ) : ℂ))
    (Φ := Complex.sin) (Φ1 := Complex.cos) (Φ2 := fun w => -Complex.sin w)
    (f := fun t => mathieuCe (2 * n + 1) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuCe (2 * n + 1) z (h ^ 2)) t)
    (a := mathieuA (2 * n + 1) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    p1a2_hd_one_z p1a2_hd_zero_z p1a2_hd_one_t p1a2_hd_zero_t
    (fun z t => ((Complex.hasDerivAt_cos z).const_mul _).mul_const _)
    (fun z t => ((Complex.hasDerivAt_sin z).neg.const_mul _).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rsin t).neg.const_mul _)
    Complex.hasDerivAt_sin Complex.hasDerivAt_cos (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop)
    (p1a2_hasDerivAt_ce _ _) (p1a2_hasDerivAt_deriv_ce _ _)
    (fun z t => by
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * (Real.cos t : ℂ) ^ 2 *
        Complex.sin (2 * H * Complex.cos z * Real.cos t)) * e1 +
        (4 * H ^ 2 * Complex.cos z ^ 2 * Complex.sin (2 * H * Complex.cos z * Real.cos t)) * e2)
    (fun z => by
      simp only [Real.sin_zero, Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.sin_zero, zero_mul, add_zero, p1a2_ce_odd_half_pi, Complex.ofReal_zero,
        p1a2_deriv_ce_zero])
  have hev : ∀ z, (fun z => ∫ t in (0 : ℝ)..π / 2, 1 * Complex.sin (2 * H * Complex.cos z *
      Real.cos t) * mathieuCe (2 * n + 1) t (h ^ 2)) (-z) = (fun z => ∫ t in (0 : ℝ)..π / 2,
      1 * Complex.sin (2 * H * Complex.cos z * Real.cos t) * mathieuCe (2 * n + 1) t (h ^ 2)) z :=
    fun z => by simp only [Complex.cos_neg]
  have hne : deriv (fun w => mathieuCe (2 * n + 1) w (h ^ 2)) (π / 2) ≠ 0 := fun h0 =>
    p1a2_ce_or_deriv_ne_zero _ _ (π / 2) (by
      have := p1a2_ce_odd_half_pi n (h ^ 2); push_cast at this; exact this) h0
  have := p1a2_finish_der_ce hG hev hne (A := -(H * mathieuFourierA (2 * n + 1) 1 (h ^ 2))) (by
    rw [(hder _).deriv, intervalIntegral.integral_congr (g := fun t : ℝ => (-2 * H) *
      (((Real.cos t : ℝ) : ℂ) * mathieuCe (2 * n + 1) t (h ^ 2))) (fun t _ => by
        simp only [Complex.cos_pi_div_two, mul_zero, zero_mul, Complex.cos_zero,
          Complex.sin_pi_div_two]
        ring)]
    rw [intervalIntegral.integral_const_mul, p1a2_quarter_A1]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring) z
  rw [← neg_div]
  simpa only [one_mul] using this

/-- **DLMF 28.10.4**: `(2/π) ∫₀^{π/2} cos z cos t cosh(2h sin z sin t) ce_{2n+1}(t, h²) dt
= A^{2n+1}_1(h²)/(2 ce_{2n+1}(0, h²)) · ce_{2n+1}(z, h²)`. -/
@[dlmf 28.10.E4]
theorem integral_cos_cosh_mathieuCe_odd (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2, Complex.cos z * Real.cos t *
        Complex.cosh (2 * h * Complex.sin z * Real.sin t) * mathieuCe (2 * n + 1) t (h ^ 2) =
      mathieuFourierA (2 * n + 1) 1 (h ^ 2) / (2 * mathieuCe (2 * n + 1) 0 (h ^ 2)) *
        mathieuCe (2 * n + 1) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  obtain ⟨hG, -⟩ := p1a2_isMathieuSolution_kernel (α := 0) (β := π / 2)
    (P := fun z t => Complex.cos z * Real.cos t) (Pz := fun z t => -Complex.sin z * Real.cos t)
    (Pzz := fun z t => -Complex.cos z * Real.cos t)
    (Pt := fun z t => Complex.cos z * -((Real.sin t : ℝ) : ℂ))
    (Ptt := fun z t => Complex.cos z * -((Real.cos t : ℝ) : ℂ))
    (u := fun z t => 2 * H * Complex.sin z * Real.sin t)
    (uz := fun z t => 2 * H * Complex.cos z * Real.sin t)
    (uzz := fun z t => 2 * H * -Complex.sin z * Real.sin t)
    (ut := fun z t => 2 * H * Complex.sin z * Real.cos t)
    (utt := fun z t => 2 * H * Complex.sin z * -((Real.sin t : ℝ) : ℂ))
    (Φ := Complex.cosh) (Φ1 := Complex.sinh) (Φ2 := Complex.cosh)
    (f := fun t => mathieuCe (2 * n + 1) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuCe (2 * n + 1) z (h ^ 2)) t)
    (a := mathieuA (2 * n + 1) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    (fun z t => (Complex.hasDerivAt_cos z).mul_const _)
    (fun z t => (Complex.hasDerivAt_sin z).neg.mul_const _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rsin t).neg.const_mul _)
    (fun z t => ((Complex.hasDerivAt_sin z).const_mul _).mul_const _)
    (fun z t => ((Complex.hasDerivAt_cos z).const_mul _).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rsin t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    Complex.hasDerivAt_cosh Complex.hasDerivAt_sinh Complex.continuous_cosh
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop)
    (p1a2_hasDerivAt_ce _ _) (p1a2_hasDerivAt_deriv_ce _ _)
    (fun z t => by
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * (Real.cos t : ℂ) ^ 2 * (Complex.cos z * Real.cos t *
        Complex.cosh (2 * H * Complex.sin z * Real.sin t))) * e1 +
        (4 * H ^ 2 * Complex.cos z ^ 2 * (Complex.cos z * Real.cos t *
          Complex.cosh (2 * H * Complex.sin z * Real.sin t))) * e2)
    (fun z => by
      simp only [Real.sin_zero, Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.sinh_zero, zero_mul, add_zero, p1a2_ce_odd_half_pi, p1a2_deriv_ce_zero])
  have hev : ∀ z, (fun z => ∫ t in (0 : ℝ)..π / 2, Complex.cos z * Real.cos t *
      Complex.cosh (2 * H * Complex.sin z * Real.sin t) * mathieuCe (2 * n + 1) t (h ^ 2)) (-z) =
      (fun z => ∫ t in (0 : ℝ)..π / 2, Complex.cos z * Real.cos t *
      Complex.cosh (2 * H * Complex.sin z * Real.sin t) * mathieuCe (2 * n + 1) t (h ^ 2)) z := by
    intro z
    simp only [Complex.sin_neg, Complex.cos_neg]
    congr 1; funext t
    rw [show 2 * H * -Complex.sin z * ((Real.sin t : ℝ) : ℂ) =
      -(2 * H * Complex.sin z * Real.sin t) by ring, Complex.cosh_neg]
  have hne : mathieuCe (2 * n + 1) 0 (h ^ 2) ≠ 0 := by
    rw [mathieuCe_zero]; exact Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos _ _).ne'
  have := p1a2_finish_val_ce hG hev hne (A := mathieuFourierA (2 * n + 1) 1 (h ^ 2) / 2) (by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ((Real.cos t : ℝ) : ℂ) * mathieuCe (2 * n + 1) t (h ^ 2)) (fun t _ => by
        simp only [Complex.cos_zero, Complex.sin_zero, mul_zero, zero_mul, Complex.cosh_zero]
        ring)]
    rw [p1a2_quarter_A1]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring) z
  simpa only [div_div] using this

/-- **DLMF 28.10.5**: `(2/π) ∫₀^{π/2} sinh(2h sin z sin t) se_{2n+1}(t, h²) dt
= h B^{2n+1}_1(h²)/se'_{2n+1}(0, h²) · se_{2n+1}(z, h²)`. -/
@[dlmf 28.10.E5]
theorem integral_sinh_mathieuSe_odd (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2,
        Complex.sinh (2 * h * Complex.sin z * Real.sin t) * mathieuSe (2 * n + 1) t (h ^ 2) =
      h * mathieuFourierB (2 * n + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuSe (2 * n + 1) w (h ^ 2)) 0 * mathieuSe (2 * n + 1) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  obtain ⟨hG, hder⟩ := p1a2_isMathieuSolution_kernel (α := 0) (β := π / 2)
    (P := fun _ _ => 1) (Pz := fun _ _ => 0) (Pzz := fun _ _ => 0) (Pt := fun _ _ => 0)
    (Ptt := fun _ _ => 0)
    (u := fun z t => 2 * H * Complex.sin z * Real.sin t)
    (uz := fun z t => 2 * H * Complex.cos z * Real.sin t)
    (uzz := fun z t => 2 * H * -Complex.sin z * Real.sin t)
    (ut := fun z t => 2 * H * Complex.sin z * Real.cos t)
    (utt := fun z t => 2 * H * Complex.sin z * -((Real.sin t : ℝ) : ℂ))
    (Φ := Complex.sinh) (Φ1 := Complex.cosh) (Φ2 := Complex.sinh)
    (f := fun t => mathieuSe (2 * n + 1) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuSe (2 * n + 1) z (h ^ 2)) t)
    (a := mathieuB (2 * n + 1) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    p1a2_hd_one_z p1a2_hd_zero_z p1a2_hd_one_t p1a2_hd_zero_t
    (fun z t => ((Complex.hasDerivAt_sin z).const_mul _).mul_const _)
    (fun z t => ((Complex.hasDerivAt_cos z).const_mul _).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rsin t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    Complex.hasDerivAt_sinh Complex.hasDerivAt_cosh Complex.continuous_sinh
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop)
    (p1a2_hasDerivAt_se _ _) (p1a2_hasDerivAt_deriv_se _ _)
    (fun z t => by
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * (Real.cos t : ℂ) ^ 2 *
        Complex.sinh (2 * H * Complex.sin z * Real.sin t)) * e1 +
        (4 * H ^ 2 * Complex.cos z ^ 2 * Complex.sinh (2 * H * Complex.sin z * Real.sin t)) * e2)
    (fun z => by
      simp only [Real.sin_zero, Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero,
        Complex.sinh_zero, zero_mul, add_zero, p1a2_deriv_se_odd_half_pi, p1a2_se_zero])
  have hodd : ∀ z, (fun z => ∫ t in (0 : ℝ)..π / 2, 1 * Complex.sinh (2 * H * Complex.sin z *
      Real.sin t) * mathieuSe (2 * n + 1) t (h ^ 2)) (-z) = -(fun z => ∫ t in (0 : ℝ)..π / 2,
      1 * Complex.sinh (2 * H * Complex.sin z * Real.sin t) *
        mathieuSe (2 * n + 1) t (h ^ 2)) z := by
    intro z
    simp only [Complex.sin_neg]
    rw [← intervalIntegral.integral_neg]
    congr 1; funext t
    rw [show 2 * H * -Complex.sin z * ((Real.sin t : ℝ) : ℂ) =
      -(2 * H * Complex.sin z * Real.sin t) by ring, Complex.sinh_neg]
    ring
  have hne : deriv (fun w => mathieuSe (2 * n + 1) w (h ^ 2)) 0 ≠ 0 := by
    rw [deriv_mathieuSe_zero]; exact Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos _ _).ne'
  have := p1a2_finish_der_se hG hodd hne (A := H * mathieuFourierB (2 * n + 1) 1 (h ^ 2)) (by
    rw [(hder _).deriv, intervalIntegral.integral_congr (g := fun t : ℝ => (2 * H) *
      (((Real.sin t : ℝ) : ℂ) * mathieuSe (2 * n + 1) t (h ^ 2))) (fun t _ => by
        simp only [Complex.cos_zero, Complex.sin_zero, mul_zero, zero_mul, Complex.cosh_zero]
        ring)]
    rw [intervalIntegral.integral_const_mul, p1a2_quarter_B1]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring) z
  simpa only [one_mul] using this

/-- **DLMF 28.10.6**: `(2/π) ∫₀^{π/2} sin z sin t cos(2h cos z cos t) se_{2n+1}(t, h²) dt
= B^{2n+1}_1(h²)/(2 se_{2n+1}(π/2, h²)) · se_{2n+1}(z, h²)`. -/
@[dlmf 28.10.E6]
theorem integral_sin_cos_mathieuSe_odd (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2, Complex.sin z * Real.sin t *
        Complex.cos (2 * h * Complex.cos z * Real.cos t) * mathieuSe (2 * n + 1) t (h ^ 2) =
      mathieuFourierB (2 * n + 1) 1 (h ^ 2) / (2 * mathieuSe (2 * n + 1) (π / 2) (h ^ 2)) *
        mathieuSe (2 * n + 1) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  obtain ⟨hG, -⟩ := p1a2_isMathieuSolution_kernel (α := 0) (β := π / 2)
    (P := fun z t => Complex.sin z * Real.sin t) (Pz := fun z t => Complex.cos z * Real.sin t)
    (Pzz := fun z t => -Complex.sin z * Real.sin t)
    (Pt := fun z t => Complex.sin z * Real.cos t)
    (Ptt := fun z t => Complex.sin z * -((Real.sin t : ℝ) : ℂ))
    (u := fun z t => 2 * H * Complex.cos z * Real.cos t)
    (uz := fun z t => 2 * H * -Complex.sin z * Real.cos t)
    (uzz := fun z t => 2 * H * -Complex.cos z * Real.cos t)
    (ut := fun z t => 2 * H * Complex.cos z * -((Real.sin t : ℝ) : ℂ))
    (utt := fun z t => 2 * H * Complex.cos z * -((Real.cos t : ℝ) : ℂ))
    (Φ := Complex.cos) (Φ1 := fun w => -Complex.sin w) (Φ2 := fun w => -Complex.cos w)
    (f := fun t => mathieuSe (2 * n + 1) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuSe (2 * n + 1) z (h ^ 2)) t)
    (a := mathieuB (2 * n + 1) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    (fun z t => (Complex.hasDerivAt_sin z).mul_const _)
    (fun z t => (Complex.hasDerivAt_cos z).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rsin t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    (fun z t => ((Complex.hasDerivAt_cos z).const_mul _).mul_const _)
    (fun z t => ((Complex.hasDerivAt_sin z).neg.const_mul _).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rsin t).neg.const_mul _)
    Complex.hasDerivAt_cos (fun w => (Complex.hasDerivAt_sin w).neg) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop)
    (p1a2_hasDerivAt_se _ _) (p1a2_hasDerivAt_deriv_se _ _)
    (fun z t => by
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * (Real.cos t : ℂ) ^ 2 * (Complex.sin z * Real.sin t *
        Complex.cos (2 * H * Complex.cos z * Real.cos t))) * e1 +
        (4 * H ^ 2 * Complex.cos z ^ 2 * (Complex.sin z * Real.sin t *
          Complex.cos (2 * H * Complex.cos z * Real.cos t))) * e2)
    (fun z => by
      simp only [Real.sin_zero, Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.sin_zero, zero_mul, add_zero, p1a2_deriv_se_odd_half_pi, p1a2_se_zero])
  have hodd : ∀ z, (fun z => ∫ t in (0 : ℝ)..π / 2, Complex.sin z * Real.sin t *
      Complex.cos (2 * H * Complex.cos z * Real.cos t) * mathieuSe (2 * n + 1) t (h ^ 2)) (-z) =
      -(fun z => ∫ t in (0 : ℝ)..π / 2, Complex.sin z * Real.sin t *
      Complex.cos (2 * H * Complex.cos z * Real.cos t) * mathieuSe (2 * n + 1) t (h ^ 2)) z := by
    intro z
    simp only [Complex.sin_neg, Complex.cos_neg]
    rw [← intervalIntegral.integral_neg]
    congr 1; funext t
    ring
  have hne : mathieuSe (2 * n + 1) (π / 2) (h ^ 2) ≠ 0 := fun h0 =>
    p1a2_se_or_deriv_ne_zero _ _ (π / 2) h0 (by
      have := p1a2_deriv_se_odd_half_pi n (h ^ 2); push_cast at this; exact this)
  have := p1a2_finish_val_se hG hodd hne (A := mathieuFourierB (2 * n + 1) 1 (h ^ 2) / 2) (by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ((Real.sin t : ℝ) : ℂ) * mathieuSe (2 * n + 1) t (h ^ 2)) (fun t _ => by
        simp only [Complex.sin_pi_div_two, Complex.cos_pi_div_two, mul_zero, zero_mul,
          Complex.cos_zero]
        ring)]
    rw [p1a2_quarter_B1]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring) z
  simpa only [div_div] using this

/-- **DLMF 28.10.7**: `(2/π) ∫₀^{π/2} sin z sin t sin(2h cos z cos t) se_{2n+2}(t, h²) dt
= -h B^{2n+2}_2(h²)/(2 se'_{2n+2}(π/2, h²)) · se_{2n+2}(z, h²)`. -/
@[dlmf 28.10.E7]
theorem integral_sin_sin_mathieuSe_even (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2, Complex.sin z * Real.sin t *
        Complex.sin (2 * h * Complex.cos z * Real.cos t) * mathieuSe (2 * n + 2) t (h ^ 2) =
      -(h * mathieuFourierB (2 * n + 2) 2 (h ^ 2) /
        (2 * deriv (fun w => mathieuSe (2 * n + 2) w (h ^ 2)) (π / 2))) *
        mathieuSe (2 * n + 2) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  obtain ⟨hG, hder⟩ := p1a2_isMathieuSolution_kernel (α := 0) (β := π / 2)
    (P := fun z t => Complex.sin z * Real.sin t) (Pz := fun z t => Complex.cos z * Real.sin t)
    (Pzz := fun z t => -Complex.sin z * Real.sin t)
    (Pt := fun z t => Complex.sin z * Real.cos t)
    (Ptt := fun z t => Complex.sin z * -((Real.sin t : ℝ) : ℂ))
    (u := fun z t => 2 * H * Complex.cos z * Real.cos t)
    (uz := fun z t => 2 * H * -Complex.sin z * Real.cos t)
    (uzz := fun z t => 2 * H * -Complex.cos z * Real.cos t)
    (ut := fun z t => 2 * H * Complex.cos z * -((Real.sin t : ℝ) : ℂ))
    (utt := fun z t => 2 * H * Complex.cos z * -((Real.cos t : ℝ) : ℂ))
    (Φ := Complex.sin) (Φ1 := Complex.cos) (Φ2 := fun w => -Complex.sin w)
    (f := fun t => mathieuSe (2 * n + 2) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuSe (2 * n + 2) z (h ^ 2)) t)
    (a := mathieuB (2 * n + 2) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    (fun z t => (Complex.hasDerivAt_sin z).mul_const _)
    (fun z t => (Complex.hasDerivAt_cos z).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rsin t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    (fun z t => ((Complex.hasDerivAt_cos z).const_mul _).mul_const _)
    (fun z t => ((Complex.hasDerivAt_sin z).neg.const_mul _).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rsin t).neg.const_mul _)
    Complex.hasDerivAt_sin Complex.hasDerivAt_cos (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop)
    (p1a2_hasDerivAt_se _ _) (p1a2_hasDerivAt_deriv_se _ _)
    (fun z t => by
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * (Real.cos t : ℂ) ^ 2 * (Complex.sin z * Real.sin t *
        Complex.sin (2 * H * Complex.cos z * Real.cos t))) * e1 +
        (4 * H ^ 2 * Complex.cos z ^ 2 * (Complex.sin z * Real.sin t *
          Complex.sin (2 * H * Complex.cos z * Real.cos t))) * e2)
    (fun z => by
      simp only [Real.sin_zero, Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.sin_zero, zero_mul, add_zero, p1a2_se_even_half_pi, p1a2_se_zero])
  have hodd : ∀ z, (fun z => ∫ t in (0 : ℝ)..π / 2, Complex.sin z * Real.sin t *
      Complex.sin (2 * H * Complex.cos z * Real.cos t) * mathieuSe (2 * n + 2) t (h ^ 2)) (-z) =
      -(fun z => ∫ t in (0 : ℝ)..π / 2, Complex.sin z * Real.sin t *
      Complex.sin (2 * H * Complex.cos z * Real.cos t) * mathieuSe (2 * n + 2) t (h ^ 2)) z := by
    intro z
    simp only [Complex.sin_neg, Complex.cos_neg]
    rw [← intervalIntegral.integral_neg]
    congr 1; funext t
    ring
  have hne : deriv (fun w => mathieuSe (2 * n + 2) w (h ^ 2)) (π / 2) ≠ 0 := fun h0 =>
    p1a2_se_or_deriv_ne_zero _ _ (π / 2) (by
      have := p1a2_se_even_half_pi n (h ^ 2); push_cast at this; exact this) h0
  have := p1a2_finish_der_se hG hodd hne (A := -(H * mathieuFourierB (2 * n + 2) 2 (h ^ 2) / 2))
    (by
    rw [(hder _).deriv, intervalIntegral.integral_congr (g := fun t : ℝ => (-2 * H) *
      (((Real.sin t : ℝ) : ℂ) * ((Real.cos t : ℝ) : ℂ) * mathieuSe (2 * n + 2) t (h ^ 2)))
      (fun t _ => by
        simp only [Complex.sin_pi_div_two, Complex.cos_pi_div_two, mul_zero, zero_mul,
          Complex.cos_zero]
        ring)]
    rw [intervalIntegral.integral_const_mul, p1a2_quarter_B2]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring) z
  rw [this]
  ring

/-- **DLMF 28.10.8**: `(2/π) ∫₀^{π/2} cos z cos t sinh(2h sin z sin t) se_{2n+2}(t, h²) dt
= h B^{2n+2}_2(h²)/(2 se'_{2n+2}(0, h²)) · se_{2n+2}(z, h²)`. -/
@[dlmf 28.10.E8]
theorem integral_cos_sinh_mathieuSe_even (n : ℕ) (h : ℝ) (z : ℂ) :
    2 / π * ∫ t in (0 : ℝ)..π / 2, Complex.cos z * Real.cos t *
        Complex.sinh (2 * h * Complex.sin z * Real.sin t) * mathieuSe (2 * n + 2) t (h ^ 2) =
      h * mathieuFourierB (2 * n + 2) 2 (h ^ 2) /
        (2 * deriv (fun w => mathieuSe (2 * n + 2) w (h ^ 2)) 0) *
        mathieuSe (2 * n + 2) z (h ^ 2) := by
  set H : ℂ := (h : ℂ) with hH
  have hQ : (((h ^ 2 : ℝ)) : ℂ) = H ^ 2 := by push_cast; rfl
  obtain ⟨hG, hder⟩ := p1a2_isMathieuSolution_kernel (α := 0) (β := π / 2)
    (P := fun z t => Complex.cos z * Real.cos t) (Pz := fun z t => -Complex.sin z * Real.cos t)
    (Pzz := fun z t => -Complex.cos z * Real.cos t)
    (Pt := fun z t => Complex.cos z * -((Real.sin t : ℝ) : ℂ))
    (Ptt := fun z t => Complex.cos z * -((Real.cos t : ℝ) : ℂ))
    (u := fun z t => 2 * H * Complex.sin z * Real.sin t)
    (uz := fun z t => 2 * H * Complex.cos z * Real.sin t)
    (uzz := fun z t => 2 * H * -Complex.sin z * Real.sin t)
    (ut := fun z t => 2 * H * Complex.sin z * Real.cos t)
    (utt := fun z t => 2 * H * Complex.sin z * -((Real.sin t : ℝ) : ℂ))
    (Φ := Complex.sinh) (Φ1 := Complex.cosh) (Φ2 := Complex.sinh)
    (f := fun t => mathieuSe (2 * n + 2) t (h ^ 2))
    (f' := fun t => deriv (fun z => mathieuSe (2 * n + 2) z (h ^ 2)) t)
    (a := mathieuB (2 * n + 2) (h ^ 2)) (q := ((h ^ 2 : ℝ) : ℂ))
    (fun z t => (Complex.hasDerivAt_cos z).mul_const _)
    (fun z t => (Complex.hasDerivAt_sin z).neg.mul_const _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rsin t).neg.const_mul _)
    (fun z t => ((Complex.hasDerivAt_sin z).const_mul _).mul_const _)
    (fun z t => ((Complex.hasDerivAt_cos z).const_mul _).mul_const _)
    (fun z t => (p1a2_hasDerivAt_rsin t).const_mul _)
    (fun z t => (p1a2_hasDerivAt_rcos t).const_mul _)
    Complex.hasDerivAt_sinh Complex.hasDerivAt_cosh Complex.continuous_sinh
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop) (fun z => by fun_prop)
    (p1a2_hasDerivAt_se _ _) (p1a2_hasDerivAt_deriv_se _ _)
    (fun z t => by
      rw [hQ, Complex.cos_two_mul, Complex.cos_two_mul, ← Complex.ofReal_cos]
      have e1 := Complex.sin_sq_add_cos_sq z
      have e2 := Complex.sin_sq_add_cos_sq (t : ℂ)
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at e2
      linear_combination (-4 * H ^ 2 * (Real.cos t : ℂ) ^ 2 * (Complex.cos z * Real.cos t *
        Complex.sinh (2 * H * Complex.sin z * Real.sin t))) * e1 +
        (4 * H ^ 2 * Complex.cos z ^ 2 * (Complex.cos z * Real.cos t *
          Complex.sinh (2 * H * Complex.sin z * Real.sin t))) * e2)
    (fun z => by
      simp only [Real.sin_zero, Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.sinh_zero, zero_mul, add_zero, p1a2_se_even_half_pi, p1a2_se_zero])
  have hodd : ∀ z, (fun z => ∫ t in (0 : ℝ)..π / 2, Complex.cos z * Real.cos t *
      Complex.sinh (2 * H * Complex.sin z * Real.sin t) * mathieuSe (2 * n + 2) t (h ^ 2)) (-z) =
      -(fun z => ∫ t in (0 : ℝ)..π / 2, Complex.cos z * Real.cos t *
      Complex.sinh (2 * H * Complex.sin z * Real.sin t) * mathieuSe (2 * n + 2) t (h ^ 2)) z := by
    intro z
    simp only [Complex.sin_neg, Complex.cos_neg]
    rw [← intervalIntegral.integral_neg]
    congr 1; funext t
    rw [show 2 * H * -Complex.sin z * ((Real.sin t : ℝ) : ℂ) =
      -(2 * H * Complex.sin z * Real.sin t) by ring, Complex.sinh_neg]
    ring
  have hne : deriv (fun w => mathieuSe (2 * n + 2) w (h ^ 2)) 0 ≠ 0 := by
    rw [deriv_mathieuSe_zero]; exact Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos _ _).ne'
  have := p1a2_finish_der_se hG hodd hne (A := H * mathieuFourierB (2 * n + 2) 2 (h ^ 2) / 2) (by
    rw [(hder _).deriv, intervalIntegral.integral_congr (g := fun t : ℝ => (2 * H) *
      (((Real.sin t : ℝ) : ℂ) * ((Real.cos t : ℝ) : ℂ) * mathieuSe (2 * n + 2) t (h ^ 2)))
      (fun t _ => by
        simp only [Complex.cos_zero, Complex.sin_zero, mul_zero, zero_mul, Complex.cosh_zero,
          Complex.sinh_zero, neg_zero]
        ring)]
    rw [intervalIntegral.integral_const_mul, p1a2_quarter_B2]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp; ring) z
  simpa only [div_div] using this

/-- **DLMF 28.10.9**: `∫₀^{π/2} J₀(2√(q(cos²τ - sin²ζ))) ce_{2n}(τ, q) dτ
= w_II(π/2; a_{2n}(q), q) ce_{2n}(ζ, q)` (real `q`, complex `ζ`). -/
@[dlmf 28.10.E9]
theorem integral_besselJ_mathieuCe_even (n : ℕ) (q : ℝ) (ζ : ℂ) :
    ∫ τ in (0 : ℝ)..π / 2, Complex.besselJ 0
        (2 * ((q : ℂ) * ((Real.cos τ : ℂ) ^ 2 - Complex.sin ζ ^ 2)) ^ (1 / 2 : ℂ)) *
        mathieuCe (2 * n) τ q =
      mathieuWII (mathieuA (2 * n) q) q (π / 2) * mathieuCe (2 * n) ζ q := by
  sorry

/-- **DLMF 28.10.10**: `∫₀^π J₀(2√q (cos τ + cos ζ)) ce_n(τ, q) dτ
= w_II(π; a_n(q), q) ce_n(ζ, q)` (real `q`, `√q` principal for `q < 0`). -/
@[dlmf 28.10.E10]
theorem integral_besselJ_mathieuCe (n : ℕ) (q : ℝ) (ζ : ℂ) :
    ∫ τ in (0 : ℝ)..π, Complex.besselJ 0
        (2 * (q : ℂ) ^ (1 / 2 : ℂ) * (Real.cos τ + Complex.cos ζ)) * mathieuCe n τ q =
      mathieuWII (mathieuA n q) q π * mathieuCe n ζ q := by
  sorry

end DLMF.Mathieu
