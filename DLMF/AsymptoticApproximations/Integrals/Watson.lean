/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import DLMF.AlgebraicAnalytic.Transforms.Fourier
public import DLMF.AsymptoticApproximations.Integrals.Basic
public import DLMFMathlib.Analysis.Asymptotics.WatsonKernel
public import DLMFMathlib.Analysis.Asymptotics.WatsonLog
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import Mathlib.Analysis.MellinTransform

/-!
# Watson's lemma and inverse Laplace transforms (DLMF §§2.3(ii), 2.4(i)–(ii))

The project's Watson lemma (`hasAsymptoticExpansion_integral_exp_smul`,
`hasAsymptoticExpansion_integral_cexp_smul_sector`, in `DLMFMathlib`) has exponents in steps of
`1`. DLMF's form 2.3.7–2.3.8 has exponents `(s + λ)/μ`, in steps of `1/μ`. This file first
proves Watson's lemma for an arbitrary sequence of exponents `eₙ` with `ℜ eₙ > 0` (the proofs
follow the project's, through its remainder bounds `isBigO_integral_exp_smul` and
`isBigO_integral_cexp_smul_sector`), then the DLMF statements:

* 2.3.1, 2.3.7–2.3.8 (real `x`), and the `laplaceTransform` form of the Chapter 1 area;
* 2.3.9 (logarithmic factor) and 2.3.10–2.3.12 (general kernel `f(xt)`, Mellin transform);
* 2.4.1 (complex `z` in a sector, complex `λ`) and the rotation of §2.4(i);
* §2.4(ii): the Laplace inversion 2.4.2–2.4.3, the inverse transform of an asymptotic
  expansion 2.4.4–2.4.5, and Haar's method 2.4.6–2.4.9.

Integrals that DLMF assumes "convergent for all sufficiently large `x`" are Lebesgue integrals
here, with the hypothesis that `e^{-ct} q(t)` is integrable on `(0, ∞)` for some `c`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Watson's lemma for a general sequence of exponents: if
`F(t) - ∑_{n<N} t^{eₙ-1} aₙ = O(t^{e_N - 1})` as `t → 0⁺` for every `N`, with all `eₙ > 0`, and
`e^{-ct} F` is integrable on `(0, ∞)`, then `∫₀^∞ e^{-xt} F(t) dt ~ ∑ Γ(eₙ) aₙ x^{-eₙ}` as
`x → +∞`. (The `eₙ` need not be increasing; for a genuine asymptotic expansion they are.) -/
theorem hasAsymptoticExpansion_integral_exp_smul_rpow_seq {F : ℝ → E} {a : ℕ → E}
    {e : ℕ → ℝ} {c : ℝ} (he : ∀ n, 0 < e n)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0))
    (hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ range N, t ^ (e n - 1) • a n) =O[𝓝[>] 0]
      fun t => t ^ (e N - 1)) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => x ^ (-e n))
      (fun n => Real.Gamma (e n) • a n)
      (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • F t) := by
  intro N
  set c' := max c 0 + 1 with hc'
  have hcc' : c ≤ c' := by linarith [le_max_left c 0]
  have hc'0 : 0 < c' := by linarith [le_max_right c 0]
  set G : ℝ → E := fun t => F t - ∑ n ∈ range N, t ^ (e n - 1) • a n with hG
  have hpow : ∀ (w s : ℝ), 0 < w → 0 < s → ∀ b : E,
      IntegrableOn (fun t : ℝ => Real.exp (-w * t) • (t ^ (s - 1) • b)) (Ioi 0) := by
    intro w s hw hs b
    exact IntegrableOn.congr_fun ((integrableOn_exp_neg_mul_mul_rpow_sub_one hs hw).smul_const b)
      (fun t _ => by simp only [smul_smul]) measurableSet_Ioi
  have hintG : IntegrableOn (fun t => Real.exp (-c' * t) • G t) (Ioi 0) := by
    have h := (hint.exp_neg_mul_smul_of_le hcc').sub (integrable_finsetSum (range N)
      fun (n : ℕ) _ => (hpow c' (e n) hc'0 (he n) (a n)))
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [hG, smul_sub, Finset.smul_sum, Pi.sub_apply]
  refine (isBigO_integral_exp_smul (he N) hintG (by simpa [hG] using hF N)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop c'] with z hz
  have hzc : c ≤ z := hcc'.trans hz
  have hz0 : 0 < z := hc'0.trans_le hz
  simp only [hG, smul_sub, Finset.smul_sum]
  rw [integral_sub (hint.exp_neg_mul_smul_of_le hzc) (integrable_finsetSum (range N)
    fun (n : ℕ) _ => hpow z (e n) hz0 (he n) (a n)), integral_finsetSum _
    fun (n : ℕ) _ => hpow z (e n) hz0 (he n) (a n)]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  simp_rw [smul_smul]
  rw [integral_smul_const, integral_exp_neg_mul_mul_rpow_sub_one (he n) hz0, mul_comm]

/-- Identity under the stated parameter and domain assumptions: `(s + lam - mu) / mu = (s + lam) /
mu - 1`. -/
private lemma g2a_exp_eq {lam mu : ℝ} (hmu : 0 < mu) (s : ℝ) :
    (s + lam - mu) / mu = (s + lam) / mu - 1 := by
  field_simp

/-- DLMF 2.3.1, 2.3.7–2.3.8 (**Watson's lemma**): if the Laplace transform 2.3.1 converges for
large `x` (here: `e^{-ct} q(t)` is integrable on `(0, ∞)`) and
`q(t) ∼ ∑ aₛ t^{(s+λ-μ)/μ}` as `t → 0⁺` (2.3.7) with `λ, μ > 0`, then
`∫₀^∞ e^{-xt} q(t) dt ∼ ∑ Γ((s+λ)/μ) aₛ x^{-(s+λ)/μ}` as `x → +∞` (2.3.8). The coefficients
lie in any real Banach space (so `q` may be complex-valued). -/
@[dlmf 2.3.E1, dlmf 2.3.E7, dlmf 2.3.E8, dlmf 2.3.ii]
theorem watson_lemma {q : ℝ → E} {a : ℕ → E} {lam mu c : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0))
    (hq : HasAsymptoticExpansion (𝓝[>] 0) (fun (s : ℕ) (t : ℝ) => t ^ (((s : ℝ) + lam - mu) / mu))
      a q) :
    HasAsymptoticExpansion atTop (fun (s : ℕ) (x : ℝ) => x ^ (-(((s : ℝ) + lam) / mu)))
      (fun s => Real.Gamma (((s : ℝ) + lam) / mu) • a s)
      (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • q t) := by
  refine hasAsymptoticExpansion_integral_exp_smul_rpow_seq (e := fun s => ((s : ℝ) + lam) / mu)
    (fun n => by positivity) hint fun N => ?_
  simpa only [g2a_exp_eq hmu] using hq N

end Real

/-- DLMF 2.3.1, 2.3.8 for the Laplace transform `laplaceTransform q x = ∫₀^∞ e^{-xt} q(t) dt`
of DLMF 1.14.17 (`DLMF.AlgebraicAnalytic.laplaceTransform`), for complex-valued `q` and real
`x`. -/
@[dlmf 2.3.E1, dlmf 2.3.E8]
theorem watson_lemma_laplaceTransform {q : ℝ → ℂ} {a : ℕ → ℂ} {lam mu c : ℝ} (hlam : 0 < lam)
    (hmu : 0 < mu) (hint : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0))
    (hq : HasAsymptoticExpansion (𝓝[>] 0) (fun (s : ℕ) (t : ℝ) => t ^ (((s : ℝ) + lam - mu) / mu))
      a q) :
    HasAsymptoticExpansion atTop (fun (s : ℕ) (x : ℝ) => x ^ (-(((s : ℝ) + lam) / mu)))
      (fun s => Real.Gamma (((s : ℝ) + lam) / mu) • a s)
      (fun x : ℝ => DLMF.AlgebraicAnalytic.laplaceTransform q x) := by
  refine (watson_lemma hlam hmu hint hq).congr' (Eventually.of_forall fun x => ?_)
  unfold DLMF.AlgebraicAnalytic.laplaceTransform
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [Complex.real_smul, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- DLMF 2.3.9: Watson's lemma with a logarithmic factor. Under the hypotheses of 2.3.8, and if
`e^{-ct} q(t) ln t` is also integrable on `(0, ∞)`,
`∫₀^∞ e^{-xt} q(t) ln t dt ∼ ∑ Γ'((s+λ)/μ) aₛ x^{-(s+λ)/μ} - (ln x) ∑ Γ((s+λ)/μ) aₛ x^{-(s+λ)/μ}`
as `x → +∞`, in the sense that the remainder after `N` terms of both sums is
`O(x^{-(N+λ)/μ} ln x)`. -/
@[dlmf 2.3.E9]
theorem watson_lemma_log {q : ℝ → ℝ} {a : ℕ → ℝ} {lam mu c : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)

    (hintlog : IntegrableOn (fun t => Real.exp (-c * t) * q t * Real.log t) (Ioi 0))
    (hq : HasAsymptoticExpansion (𝓝[>] 0) (fun (s : ℕ) (t : ℝ) => t ^ (((s : ℝ) + lam - mu) / mu))
      a q) (N : ℕ) :
    (fun x : ℝ => (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * q t * Real.log t) -
        ∑ s ∈ range N, (deriv Real.Gamma (((s : ℝ) + lam) / mu) -
          Real.log x * Real.Gamma (((s : ℝ) + lam) / mu)) * a s * x ^ (-(((s : ℝ) + lam) / mu)))
      =O[atTop] fun x => x ^ (-(((N : ℝ) + lam) / mu)) * Real.log x := by
  refine isBigO_integral_exp_mul_log_sub_sum
    (e := fun n => ((n : ℝ) + lam) / mu) (fun n => by positivity)
    (fun n => by push_cast; exact div_lt_div_of_pos_right (by linarith) hmu) hintlog
    (fun M => ?_) N
  simpa only [g2a_exp_eq hmu, smul_eq_mul] using hq M

/-- DLMF 2.3.10–2.3.12: Watson's lemma for a general kernel. Let `q` satisfy 2.3.7 with
`λ, μ > 0`, be locally integrable on `(0, ∞)` (DLMF: piecewise continuous) and satisfy
`q(t) = O(exp(b t^κ))` as `t → +∞` (2.3.11); let `f` be measurable with
`|f(t)| ≤ A exp(-a t^κ)` for `t ≥ 0` (2.3.10), `A, a, b, κ > 0`. Then
`∫₀^∞ f(xt) q(t) dt ∼ ∑ 𝓜f((s+λ)/μ) aₛ x^{-(s+λ)/μ}` as `x → +∞` (2.3.12), with Mathlib's Mellin
transform `mellin f`. -/
@[dlmf 2.3.E10, dlmf 2.3.E11, dlmf 2.3.E12]
theorem watson_lemma_kernel {f q : ℝ → ℂ} {a : ℕ → ℂ} {lam mu A a' b κ : ℝ} (hlam : 0 < lam)
    (hmu : 0 < mu) (hA : 0 < A) (ha' : 0 < a') (hb : 0 < b) (hκ : 0 < κ)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a' * t ^ κ))
    (hqi : LocallyIntegrableOn q (Ioi 0))
    (hqb : q =O[atTop] fun t => Real.exp (b * t ^ κ))
    (hq : HasAsymptoticExpansion (𝓝[>] 0) (fun (s : ℕ) (t : ℝ) => t ^ (((s : ℝ) + lam - mu) / mu))
      a q) :
    HasAsymptoticExpansion atTop (fun (s : ℕ) (x : ℝ) => x ^ (-(((s : ℝ) + lam) / mu)))
      (fun s => mellin f ((((s : ℝ) + lam) / mu : ℝ) : ℂ) * a s)
      (fun x => ∫ t in Ioi (0 : ℝ), f (x * t) * q t) := by
  refine hasAsymptoticExpansion_integral_kernel_mul_rpow_seq
    (e := fun n => ((n : ℝ) + lam) / mu) (fun n => by positivity)
    hA.le ha' hb hκ hfm hf hqi hqb (fun N => ?_)
  simpa only [g2a_exp_eq hmu, Complex.real_smul] using hq N

section Sector

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- Watson's lemma in a sector for a general sequence of complex exponents: if
`F(t) - ∑_{n<N} t^{eₙ-1} aₙ = O(t^{ℜe_N - 1})` as `t → 0⁺` for every `N`, with `ℜ eₙ > 0`, and
`e^{-ct} F` is integrable on `(0, ∞)`, then `∫₀^∞ e^{-zt} F(t) dt ~ ∑ Γ(eₙ) aₙ z^{-eₙ}` as
`z → ∞` with `δ |z| ≤ ℜz`, `δ > 0`, principal powers. -/
theorem hasAsymptoticExpansion_integral_cexp_smul_cpow_seq {F : ℝ → V} {a : ℕ → V}
    {e : ℕ → ℂ} {c δ : ℝ} (he : ∀ n, 0 < (e n).re) (hδ : 0 < δ)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0))
    (hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ range N, ((t : ℂ) ^ (e n - 1)) • a n)
      =O[𝓝[>] 0] fun t => t ^ ((e N).re - 1)) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-e n))
      (fun n => Complex.Gamma (e n) • a n)
      (fun z => ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) • F t) := by
  intro N
  set c' := max c 0 + 1 with hc'
  have hcc' : c ≤ c' := by linarith [le_max_left c 0]
  have hc'0 : 0 < c' := by linarith [le_max_right c 0]
  set G : ℝ → V := fun t => F t - ∑ n ∈ range N, ((t : ℂ) ^ (e n - 1)) • a n with hG
  have hpowr : ∀ (n : ℕ) (b : V), IntegrableOn (fun t : ℝ => Real.exp (-c' * t) •
      (((t : ℂ) ^ (e n - 1)) • b)) (Ioi 0) := fun n b =>
    IntegrableOn.congr_fun ((integrableOn_exp_neg_mul_smul_cpow_sub_one (he n) hc'0).smul_const b)
      (fun t _ => by rw [smul_assoc]) measurableSet_Ioi
  have hpowz : ∀ (n : ℕ) (b : V) (z : ℂ), c' ≤ z.re → IntegrableOn (fun t : ℝ =>
      Complex.exp (-(z * t)) • (((t : ℂ) ^ (e n - 1)) • b)) (Ioi 0) :=
    fun n b z hz => integrableOn_cexp_neg_mul_smul_of_le (hpowr n b) hz
  have hintG : IntegrableOn (fun t => Real.exp (-c' * t) • G t) (Ioi 0) := by
    have h := (hint.exp_neg_mul_smul_of_le hcc').sub (integrable_finsetSum (range N)
      fun (n : ℕ) _ => hpowr n (a n))
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [hG, smul_sub, Finset.smul_sum, Pi.sub_apply]
  have hb := isBigO_integral_cexp_smul_sector (s := (e N).re) (he N) hδ hintG
    (by simpa [hG] using hF N)
  have hnorm := isBigO_norm_rpow_cpow_neg_sector δ (e N)
  refine (hb.trans hnorm).congr' ?_ EventuallyEq.rfl
  refine eventually_sectorAtTop (R := c' / δ) fun z hzR hzs => ?_
  have hzc' : c' ≤ z.re := by rw [div_le_iff₀ hδ] at hzR; linarith
  have hzc : c ≤ z.re := hcc'.trans hzc'
  have hz0 : 0 < z.re := hc'0.trans_le hzc'
  simp only [hG, smul_sub, Finset.smul_sum]
  rw [integral_sub (integrableOn_cexp_neg_mul_smul_of_le hint hzc)
    (integrable_finsetSum (range N) fun (n : ℕ) _ => hpowz n (a n) z hzc'),
    integral_finsetSum _ fun (n : ℕ) _ => hpowz n (a n) z hzc']
  congr 1
  refine sum_congr rfl fun n _ => ?_
  simp_rw [← smul_assoc]
  rw [integral_smul_const]
  congr 1
  rw [smul_eq_mul, mul_comm, ← integral_cpow_mul_cexp_neg_mul_Ioi (he n) hz0]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, mul_comm]

/-- DLMF 2.4.1 (**Watson's lemma for complex `z`**): with `λ` complex, `ℜλ > 0`, `μ > 0`, if
`q(t) ∼ ∑ aₛ t^{(s+λ-μ)/μ}` as `t → 0⁺` (2.3.7; principal powers of `t > 0`) and `e^{-ct} q(t)`
is integrable on `(0, ∞)`, then `∫₀^∞ e^{-zt} q(t) dt ∼ ∑ Γ((s+λ)/μ) aₛ z^{-(s+λ)/μ}` as
`z → ∞` in the sector `|ph z| ≤ ½π - δ`, with principal powers `z^{(s+λ)/μ}`. The sector is
written `δ' |z| ≤ ℜz` (`Asymptotics.sectorAtTop δ'`, `δ' = sin δ > 0`). -/
@[dlmf 2.4.E1, dlmf 2.4.i]
theorem watson_lemma_sector {q : ℝ → V} {a : ℕ → V} {lam : ℂ} {mu c δ : ℝ} (hlam : 0 < lam.re)
    (hmu : 0 < mu) (hδ : 0 < δ) (hint : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0))
    (hq : HasAsymptoticExpansion (𝓝[>] 0)
      (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (((s : ℂ) + lam - mu) / mu)) a q) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (s : ℕ) (z : ℂ) => z ^ (-(((s : ℂ) + lam) / mu)))
      (fun s => Complex.Gamma (((s : ℂ) + lam) / mu) • a s)
      (fun z => ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) • q t) := by
  have hmu' : (mu : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmu.ne'
  have hre : ∀ n : ℕ, (((n : ℂ) + lam) / mu).re = ((n : ℝ) + lam.re) / mu := fun n => by
    rw [Complex.div_ofReal_re]; simp
  refine hasAsymptoticExpansion_integral_cexp_smul_cpow_seq (e := fun s => ((s : ℂ) + lam) / mu)
    (fun n => by rw [hre]; positivity) hδ hint fun N => ?_
  have h1 : ∀ s : ℕ, ((s : ℂ) + lam - mu) / mu = ((s : ℂ) + lam) / mu - 1 := fun s => by
    field_simp
  have h2 := hq N
  simp only [h1] at h2
  refine h2.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : (0 : ℝ) < t := ht
  rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  simp [hre]

/-- DLMF §2.4(i), rotation of the integration path: let `q` be defined on the ray
`ph t = θ`, `|θ| < ½π`, with `q(r e^{iθ}) ∼ ∑ aₛ (r e^{iθ})^{(s+λ-μ)/μ}` as `r → 0⁺` (principal
powers) and `e^{-cr} q(r e^{iθ})` integrable on `(0, ∞)`. Then the rotated Laplace integral
`∫₀^{∞e^{iθ}} e^{-zt} q(t) dt = e^{iθ} ∫₀^∞ e^{-z r e^{iθ}} q(r e^{iθ}) dr` has the expansion 2.4.1
as `z → ∞` in the closed sector `δ |z| ≤ ℜ(z e^{iθ})`, that is `|ph z + θ| ≤ arccos δ`. When `q`
is analytic in `α₁ < ph t < α₂` with `q(t) = O(e^{σ|t|})` there, the rotated integrals continue
the Laplace transform analytically, so 2.4.1 holds in closed sectors properly interior to
`-α₂ - ½π < ph z < -α₁ + ½π`. The project's version with exponents `n + μ` is
`hasAsymptoticExpansion_integral_cexp_smul_rotate_comap`. -/
@[dlmf 2.4.i]
theorem watson_lemma_rotate {q : ℂ → V} {a : ℕ → V} {lam : ℂ} {mu c δ θ : ℝ}
    (hθ : |θ| < π / 2) (hlam : 0 < lam.re) (hmu : 0 < mu) (hδ : 0 < δ)
    (hint : IntegrableOn (fun r : ℝ => Real.exp (-c * r) • q (r * Complex.exp (θ * I))) (Ioi 0))
    (hq : HasAsymptoticExpansion (𝓝[>] 0)
      (fun (s : ℕ) (r : ℝ) => ((r : ℂ) * Complex.exp (θ * I)) ^ (((s : ℂ) + lam - mu) / mu)) a
      fun r => q (r * Complex.exp (θ * I))) :
    HasAsymptoticExpansion
      (comap (fun z : ℂ => z * Complex.exp (θ * I)) (sectorAtTop δ))
      (fun (s : ℕ) (z : ℂ) => z ^ (-(((s : ℂ) + lam) / mu)))
      (fun s => Complex.Gamma (((s : ℂ) + lam) / mu) • a s)
      (fun z => Complex.exp (θ * I) • ∫ r in Ioi (0 : ℝ),
        Complex.exp (-(z * Complex.exp (θ * I) * r)) • q (r * Complex.exp (θ * I))) := by
  sorry

end Sector

/-! ### §2.4(ii): inverse Laplace transforms -/

/-- DLMF 2.4.2–2.4.3 (Laplace inversion, §1.14(iii)): if `q` is differentiable on `(0, ∞)` and
`e^{-ct} q(t)` is integrable there, then with `Q(z) = ∫₀^∞ e^{-zt} q(t) dt` (2.4.2),
`q(t) = (2πi)⁻¹ lim_{η→∞} ∫_{σ-iη}^{σ+iη} e^{tz} Q(z) dz` for `0 < t < ∞` and every `σ ≥ c`
(2.4.3). (DLMF takes `σ ≥ c`; for `σ = c` the transform is evaluated on the boundary line of
absolute convergence.) -/
@[dlmf 2.4.E2, dlmf 2.4.E3]
theorem laplace_inversion {q : ℝ → ℂ} {c σ t : ℝ} (hq : DifferentiableOn ℝ q (Ioi 0))
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0)) (hσ : c ≤ σ) (ht : 0 < t) :
    Tendsto (bromwichPartial (DLMF.AlgebraicAnalytic.laplaceTransform q) σ t) atTop
      (𝓝 (q t)) := by
  sorry

/-- DLMF 2.4.4–2.4.5: let `c > 0` and let `Q` be analytic in `ℜz ≥ c` with the differentiable
expansion `Q(z) ∼ ∑ Γ((s+λ)/μ) aₛ z^{-(s+λ)/μ}` as `z → ∞` there (2.4.4; `λ, μ > 0`, principal
powers), the derivative having the termwise differentiated expansion. Then the inversion
integral 2.4.5 converges at each limit, its value `q(t)` is independent of `σ ∈ [c, ∞)`, and
`q(t) ∼ ∑ aₛ t^{(s+λ-μ)/μ}` as `t → 0⁺` (2.3.7). The improper integral is the limit of
`bromwichPartial`. -/
@[dlmf 2.4.E4, dlmf 2.4.E5]
theorem inverseLaplace_of_hasAsymptoticExpansion {Q : ℂ → ℂ} {a : ℕ → ℂ} {lam mu c : ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu)
    (hQ : DifferentiableOn ℂ Q {z | c ≤ z.re})
    (hexp : HasAsymptoticExpansion (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re})
      (fun (s : ℕ) (z : ℂ) => z ^ (-(((s : ℂ) + lam) / mu)))
      (fun s => Complex.Gamma (((s : ℂ) + lam) / mu) * a s) Q)
    (hexp' : HasAsymptoticExpansion (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re})
      (fun (s : ℕ) (z : ℂ) => z ^ (-(((s : ℂ) + lam) / mu) - 1))
      (fun s => -(((s : ℂ) + lam) / mu) * Complex.Gamma (((s : ℂ) + lam) / mu) * a s)
      (deriv Q)) :
    ∃ q : ℝ → ℂ, (∀ σ, c ≤ σ → ∀ t, 0 < t → Tendsto (bromwichPartial Q σ t) atTop (𝓝 (q t))) ∧
      HasAsymptoticExpansion (𝓝[>] 0)
        (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ ((((s : ℝ) + lam - mu) / mu : ℝ) : ℂ)) a q := by
  sorry

/-- DLMF 2.4.6–2.4.7 (Haar's method): if `q(t)` and `f(t)` are the inversion integrals 2.4.3 and
2.4.6 of `Q` and of a comparison function `F` along `ℜz = σ`, then
`q(t) - f(t) = (e^{σt}/2π) lim_{η→∞} ∫_{-η}^{η} e^{itτ}(Q(σ+iτ) - F(σ+iτ)) dτ` (2.4.7). -/
@[dlmf 2.4.E6, dlmf 2.4.E7]
theorem haar_sub {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {σ t : ℝ}
    (hQi : ∀ η : ℝ, IntervalIntegrable
      (fun τ : ℝ => Complex.exp (t * (σ + τ * I)) * Q (σ + τ * I)) volume (-η) η)
    (hFi : ∀ η : ℝ, IntervalIntegrable
      (fun τ : ℝ => Complex.exp (t * (σ + τ * I)) * F (σ + τ * I)) volume (-η) η)
    (hq : Tendsto (bromwichPartial Q σ t) atTop (𝓝 (q t)))
    (hf : Tendsto (bromwichPartial F σ t) atTop (𝓝 (f t))) :
    Tendsto (fun η : ℝ => (Real.exp (σ * t) / (2 * π) : ℂ) *
        ∫ τ in -η..η, Complex.exp (I * t * τ) * (Q (σ + τ * I) - F (σ + τ * I)))
      atTop (𝓝 (q t - f t)) := by
  refine (hq.sub hf).congr fun η => ?_
  unfold bromwichPartial
  rw [← mul_sub, ← intervalIntegral.integral_sub (hQi η) (hFi η)]
  have h : ∀ τ : ℝ, Complex.exp (t * (σ + τ * I)) * Q (σ + τ * I) -
      Complex.exp (t * (σ + τ * I)) * F (σ + τ * I) =
      (Real.exp (σ * t) : ℂ) * (Complex.exp (I * t * τ) * (Q (σ + τ * I) - F (σ + τ * I))) :=
    fun τ => by
      rw [Complex.ofReal_exp, ← mul_sub, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast; ring
  simp_rw [h, intervalIntegral.integral_const_mul]
  push_cast
  ring

/-- DLMF 2.4.8 (Haar's method): in the setting of 2.4.7 on the line `ℜz = c`, if the integral
`∫_{-η}^{η} e^{itτ}(Q(c+iτ) - F(c+iτ)) dτ` converges uniformly as `η → ∞` for all sufficiently
large `t` (and the integrand is locally integrable in `τ`), then, by the Riemann–Lebesgue lemma,
`q(t) = f(t) + o(e^{ct})` as `t → +∞`. -/
@[dlmf 2.4.E8]
theorem haar_isLittleO {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {c T : ℝ} {L : ℝ → ℂ}

    (hunif : TendstoUniformlyOn (fun (η t : ℝ) =>
      ∫ τ in -η..η, Complex.exp (I * t * τ) * (Q (c + τ * I) - F (c + τ * I))) L atTop (Ici T))
    (hqf : ∀ t, T ≤ t → q t - f t = (Real.exp (c * t) / (2 * π) : ℂ) * L t) :
    (fun t => q t - f t) =o[atTop] fun t => Real.exp (c * t) := by
  have hu := hunif.tendstoUniformlyOnFilter.mono_right
    (show (atTop : Filter ℝ) ≤ 𝓟 (Ici T) from le_principal_iff.mpr (eventually_ge_atTop T))
  have hL : Tendsto L atTop (𝓝 0) := by
    refine hu.tendsto_of_eventually_tendsto ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with η hη
    let g : ℝ → ℂ := (Ioc (-η) η).indicator (fun τ => Q (c + τ * I) - F (c + τ * I))
    have h := ((DLMF.AlgebraicAnalytic.tendsto_fourierTransform_cocompact g).mono_left
      atTop_le_cocompact).const_mul (Real.sqrt (2 * π) : ℂ)
    simp only [mul_zero] at h
    refine h.congr fun t => ?_
    unfold DLMF.AlgebraicAnalytic.fourierTransform
    have he : (fun τ : ℝ => g τ * cexp (I * t * τ)) =
        (Ioc (-η) η).indicator (fun τ => cexp (I * t * τ) *
          (Q (c + τ * I) - F (c + τ * I))) := by
      ext τ
      by_cases hτ : τ ∈ Ioc (-η) η <;> simp [g, hτ, mul_comm]
    rw [he, integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -η ≤ η), ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'),
      one_mul]
  have ho : (fun t => ((2 * π : ℝ)⁻¹ : ℂ) * L t) =o[atTop] fun _ => (1 : ℝ) :=
    ((isLittleO_one_iff ℝ).mpr hL).const_mul_left _
  have hp := (isBigO_refl (fun t => Real.exp (c * t)) atTop).smul_isLittleO ho
  refine hp.congr' ?_ (Eventually.of_forall fun _ => mul_one _)
  filter_upwards [eventually_ge_atTop T] with t ht
  rw [hqf t ht, Complex.real_smul]
  push_cast
  ring

/-- DLMF 2.4.9 (Haar's method): if `Q` and `F` are holomorphic in the right half-plane
and their Fourier integrals along the vertical line, through derivative order `m`, converge
uniformly for all sufficiently large `t`, then `q(t) = f(t) + o(t^{-m} e^{ct})`.
Individual holomorphy identifies the separate derivative data with the derivatives of `Q-F`.
-/
@[dlmf 2.4.E9]
theorem haar_isLittleO_pow {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {c T : ℝ} {m : ℕ} {L : ℕ → ℝ → ℂ}
    (hd : ∀ j ≤ m, ∀ η : ℝ, IntervalIntegrable
      (fun τ : ℝ => iteratedDeriv j Q (c + τ * I) - iteratedDeriv j F (c + τ * I)) volume (-η) η)
    (hQ : DifferentiableOn ℂ Q {z | c - 1 < z.re})
    (hF : DifferentiableOn ℂ F {z | c - 1 < z.re})
    (hunif : ∀ j ≤ m, TendstoUniformlyOn (fun (η t : ℝ) => ∫ τ in -η..η,
      Complex.exp (I * t * τ) * (iteratedDeriv j Q (c + τ * I) - iteratedDeriv j F (c + τ * I)))
      (L j) atTop (Ici T))
    (hqf : ∀ t, T ≤ t → q t - f t = (Real.exp (c * t) / (2 * π) : ℂ) * L 0 t) :
    (fun t => q t - f t) =o[atTop] fun t => (t : ℝ) ^ (-(m : ℝ)) * Real.exp (c * t) := by
  sorry

end DLMF.AsymptoticApproximations
