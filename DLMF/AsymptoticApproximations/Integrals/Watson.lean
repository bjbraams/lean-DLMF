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
public import DLMFMathlib.Analysis.Fourier.DirichletKernel
public import DLMFMathlib.Analysis.Asymptotics.WatsonLog
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated
public import Mathlib.Analysis.MellinTransform

/-!
# Watson's lemma and inverse Laplace transforms (DLMF §§2.3(ii), 2.4(i)–(ii))

The project's Watson lemma (`hasAsymptoticExpansion_integral_exp_smul`,
`hasAsymptoticExpansion_integral_cexp_smul_sector`, in `DLMFMathlib`) has exponents in steps of
`1`. DLMF's form 2.3.7–2.3.8 has exponents `(s + λ)/μ`, in steps of `1/μ`. This file proves
Watson's lemma for an arbitrary sequence of exponents `eₙ` with `ℜ eₙ > 0`, then the DLMF
statements.

## Main results

* `hasAsymptoticExpansion_integral_exp_smul_rpow_seq`,
  `hasAsymptoticExpansion_integral_cexp_smul_cpow_seq`: Watson's lemma for a general sequence of
  exponents, on the real line and in a sector.
* `watson_lemma`, `watson_lemma_laplaceTransform`: DLMF 2.3.1, 2.3.7–2.3.8 for real `x`.
* `watson_lemma_log`: a logarithmic factor (DLMF 2.3.9).
* `watson_lemma_kernel`: a general kernel `f(xt)` with its Mellin transform
  (DLMF 2.3.10–2.3.12).
* `watson_lemma_sector`, `watson_lemma_rotate`: complex `z` in a sector, complex `λ`, and
  rotation of the integration path (DLMF 2.4.1, §2.4(i)).
* `laplace_inversion`, `inverseLaplace_of_hasAsymptoticExpansion`: Laplace inversion and the
  inverse transform of an asymptotic expansion (DLMF 2.4.2–2.4.5).
* `haar_sub`, `haar_isLittleO`, `haar_isLittleO_pow`, `haar_isLittleO_pow'`: Haar's method
  (DLMF 2.4.6–2.4.9).

## Implementation notes

The proofs follow the project's, through its remainder bounds `isBigO_integral_exp_smul` and
`isBigO_integral_cexp_smul_sector`. Integrals that DLMF assumes "convergent for all
sufficiently large `x`" are Lebesgue integrals here, with the hypothesis that `e^{-ct} q(t)` is
integrable on `(0, ∞)` for some `c`.
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
private lemma add_sub_div_eq_div_sub_one {lam mu : ℝ} (hmu : 0 < mu) (s : ℝ) :
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
  simpa only [add_sub_div_eq_div_sub_one hmu] using hq N

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
  simpa only [add_sub_div_eq_div_sub_one hmu, smul_eq_mul] using hq M

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
  simpa only [add_sub_div_eq_div_sub_one hmu, Complex.real_smul] using hq N

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
  have hθ1 : -π < θ := by linarith [neg_abs_le θ, Real.pi_pos]
  have hθ2 : θ ≤ π := by linarith [le_abs_self θ, Real.pi_pos]
  set x : ℕ → ℂ := fun s => ((s : ℂ) + lam - mu) / mu with hx
  -- the expansion of `G(r) = e^{iθ} q(r e^{iθ})` in powers of `r`
  have hG := (hq.smul_scale (κ := fun s => exp (θ * I * x s))
    (ψ := fun (s : ℕ) (r : ℝ) => (r : ℂ) ^ x s) fun s => by
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      rw [Complex.ofReal_mul_exp_cpow hr hθ1 hθ2]; ring).const_smul (exp (θ * I))
  have hintG : IntegrableOn (fun r : ℝ => Real.exp (-c * r) •
      (exp (θ * I) • q (r * Complex.exp (θ * I)))) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hint.smul (exp (θ * I))) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.smul_apply]
    rw [smul_comm]
  have hW := (watson_lemma_sector hlam hmu hδ hintG hG).comp_tendsto
    (tendsto_comap : Tendsto (fun z : ℂ => z * exp (θ * I))
      (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ)) (sectorAtTop δ))
  have hev : ∀ᶠ z in comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ),
      z ≠ 0 ∧ |arg z + θ| < Real.pi / 2 := by
    have h := (tendsto_comap : Tendsto (fun z : ℂ => z * exp (θ * I))
      (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ)) (sectorAtTop δ)).eventually
      (eventually_sectorAtTop (R := 1) (p := fun w : ℂ => 0 < w.re) fun w hw hws => by
        nlinarith)
    filter_upwards [h] with z hz
    refine ⟨fun h0 => by simp [h0] at hz, Complex.abs_arg_add_lt_of_re_mul_exp_pos hθ hz⟩
  refine (((hW.smul_scale (κ := fun s => exp (θ * I * (-(((s : ℂ) + lam) / mu))))
    (ψ := fun (s : ℕ) (z : ℂ) => z ^ (-(((s : ℂ) + lam) / mu))) fun s => ?_)).congr_coeff
      ?_).congr' ?_
  · filter_upwards [hev] with z hz
    rw [Complex.cpow_mul_exp_ofReal_mul_I hz.1 (by linarith [(abs_lt.mp hz.2).1, Real.pi_pos])
      (by linarith [(abs_lt.mp hz.2).2, Real.pi_pos])]
    ring
  · funext s
    have hmu' : (mu : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmu.ne'
    simp only [Pi.smul_apply, smul_smul, hx]
    congr 1
    rw [mul_left_comm, ← Complex.exp_add, ← Complex.exp_add]
    rw [show (θ : ℂ) * I * -(((s : ℂ) + lam) / mu) +
        (θ * I + θ * I * (((s : ℂ) + lam - mu) / mu)) = 0 by field_simp; ring, Complex.exp_zero,
      mul_one]
  · refine Eventually.of_forall fun z => ?_
    simp only [Function.comp]
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [smul_comm]

end Sector

/-! ### §2.4(ii): inverse Laplace transforms -/

/-- The inner Bromwich integral `∫_{-η}^{η} e^{iaτ} dτ = 2 sin(ηa)/a` for `a ≠ 0`. -/
private theorem integral_cexp_mul_I_symm {a : ℝ} (ha : a ≠ 0) (η : ℝ) :
    ∫ τ in -η..η, cexp (((a : ℂ) * I) * τ) = ((2 * (Real.sin (η * a) / a) : ℝ) : ℂ) := by
  have haI : (a : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ha) I_ne_zero
  rw [integral_exp_mul_complex haI]
  have h1 : (a : ℂ) * I * (η : ℂ) = ((η * a : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : (a : ℂ) * I * ((-η : ℝ) : ℂ) = ((-(η * a) : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, h2, exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  field_simp
  push_cast
  ring_nf
  field_simp

/-- Pointwise rearrangement of the Bromwich integrand. -/
private theorem bromwich_integrand_eq (q : ℝ → ℂ) (σ t τ u : ℝ) :
    cexp (t * (σ + τ * I)) * (cexp (-(σ + τ * I) * u) * q u) =
      cexp (σ * t) * (cexp (((t - u : ℝ) : ℂ) * I * τ) * ((Real.exp (-σ * u) : ℂ) * q u)) := by
  rw [ofReal_exp]
  calc cexp (t * (σ + τ * I)) * (cexp (-(σ + τ * I) * u) * q u)
        = cexp (t * (σ + τ * I) + -(σ + τ * I) * u) * q u := by rw [exp_add]; ring
    _ = cexp (σ * t + ((t - u : ℝ) : ℂ) * I * τ + ((-σ * u : ℝ) : ℂ)) * q u := by
        congr 2; push_cast; ring
    _ = _ := by rw [exp_add, exp_add]; ring

/-- DLMF 2.4.2–2.4.3 (Laplace inversion, §1.14(iii)): if `q` is differentiable on `(0, ∞)` and
`e^{-ct} q(t)` is integrable there, then with `Q(z) = ∫₀^∞ e^{-zt} q(t) dt` (2.4.2),
`q(t) = (2πi)⁻¹ lim_{η→∞} ∫_{σ-iη}^{σ+iη} e^{tz} Q(z) dz` for `0 < t < ∞` and every `σ ≥ c`
(2.4.3). (DLMF takes `σ ≥ c`; for `σ = c` the transform is evaluated on the boundary line of
absolute convergence.) -/
@[dlmf 2.4.E2, dlmf 2.4.E3]
theorem laplace_inversion {q : ℝ → ℂ} {c σ t : ℝ} (hq : DifferentiableOn ℝ q (Ioi 0))
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0)) (hσ : c ≤ σ) (ht : 0 < t) :
    Tendsto (bromwichPartialIntegral (DLMF.AlgebraicAnalytic.laplaceTransform q) σ t) atTop
      (𝓝 (q t)) := by
  set g : ℝ → ℂ := fun u => (Real.exp (-σ * u) : ℂ) * q u with hgdef
  have hgm : AEStronglyMeasurable g (volume.restrict (Set.Ioi 0)) :=
    ((continuous_ofReal.comp ((continuous_const.mul continuous_id).rexp)).continuousOn.mul
      hq.continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hg : IntegrableOn g (Set.Ioi 0) := by
    refine Integrable.mono hint hgm ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    simp only [hgdef, norm_mul, norm_smul, norm_real, Real.norm_eq_abs, Real.abs_exp]
    gcongr
    have : (0 : ℝ) < u := hu
    nlinarith
  set G : ℝ → ℂ := (Set.Ioi 0).indicator g with hGdef
  have hG : Integrable G := (integrable_indicator_iff measurableSet_Ioi).2 hg
  have hGt : DifferentiableAt ℝ G t := by
    have hqt : DifferentiableAt ℝ q t := hq.differentiableAt (Ioi_mem_nhds ht)
    have he : DifferentiableAt ℝ (fun u : ℝ => (Real.exp (-σ * u) : ℂ)) t := by fun_prop
    have : DifferentiableAt ℝ g t := he.mul hqt
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact Set.indicator_of_mem hu g
  have hlim := (Real.tendsto_integral_mul_sin_div_of_differentiableAt hG hGt).const_mul
    (cexp (σ * t))
  have hval : cexp (σ * t) * G t = q t := by
    rw [hGdef, indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from ht), hgdef]
    simp only [ofReal_exp, ← mul_assoc, ← exp_add]
    push_cast
    ring_nf
    simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with η hη
  have hK : ∀ u, u ≠ t → ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ τ in -η..η, cexp (((t - u : ℝ) : ℂ) * I * τ) =
        ((Real.sin (η * (t - u)) / (Real.pi * (t - u)) : ℝ) : ℂ) := by
    intro u hu
    rw [integral_cexp_mul_I_symm (sub_ne_zero.2 hu.symm)]
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    have : t - u ≠ 0 := sub_ne_zero.2 hu.symm
    push_cast
    field_simp
  set F : ℝ → ℝ → ℂ := fun τ u => cexp (t * (σ + τ * I)) * (cexp (-(σ + τ * I) * u) * q u)
    with hFdef
  have hF' : ∀ τ u, F τ u =
      cexp (σ * t) * (cexp (((t - u : ℝ) : ℂ) * I * τ) * g u) := fun τ u =>
    bromwich_integrand_eq q σ t τ u
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (-η) η)).prod (volume.restrict (Set.Ioi 0))) := by
    have hb : Integrable (fun p : ℝ × ℝ => ‖cexp (σ * t)‖ * ((1 : ℝ) * ‖g p.2‖))
        ((volume.restrict (Set.uIoc (-η) η)).prod (volume.restrict (Set.Ioi 0))) := by
      have : IsFiniteMeasure (volume.restrict (Set.uIoc (-η) η)) := ⟨by
        rw [Measure.restrict_apply_univ, Set.uIoc_of_le (by linarith)]
        exact measure_Ioc_lt_top⟩
      exact ((integrable_const (1 : ℝ)).mul_prod hg.norm).const_mul _
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Function.uncurry F = fun p : ℝ × ℝ =>
          cexp (σ * t) * (cexp (((t - p.2 : ℝ) : ℂ) * I * p.1) * g p.2) := by
        funext p; exact hF' p.1 p.2
      rw [this]
      refine aestronglyMeasurable_const.mul (Continuous.aestronglyMeasurable ?_ |>.mul hgm.comp_snd)
      fun_prop
    · simp only [Function.uncurry, hF', norm_mul, one_mul]
      rw [show ((t - p.2 : ℝ) : ℂ) * I * p.1 = ((((t - p.2) * p.1 : ℝ)) : ℂ) * I by
        push_cast; ring, norm_exp_ofReal_mul_I, one_mul]
  unfold bromwichPartialIntegral
  refine Eq.symm ?_
  calc ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ τ in -η..η,
        cexp (t * (σ + τ * I)) * DLMF.AlgebraicAnalytic.laplaceTransform q (σ + τ * I)
      = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ τ in -η..η, ∫ u in Set.Ioi 0, F τ u := by
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        simp only [DLMF.AlgebraicAnalytic.laplaceTransform, hFdef, ← integral_const_mul]
    _ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u in Set.Ioi 0, ∫ τ in -η..η, F τ u := by
        rw [intervalIntegral_integral_swap hFi]
    _ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u in Set.Ioi 0,
          cexp (σ * t) * (g u * ∫ τ in -η..η, cexp (((t - u : ℝ) : ℂ) * I * τ)) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [hF']
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext τ
        ring
    _ = cexp (σ * t) * ∫ u in Set.Ioi 0,
          g u * ((Real.sin (η * (t - u)) / (Real.pi * (t - u)) : ℝ) : ℂ) := by
        rw [← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        have hae : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))), u ≠ t :=
          ae_restrict_of_ae (by simpa using (Set.countable_singleton t).ae_notMem volume)
        filter_upwards [hae] with u hu
        rw [← hK u hu]
        ring
    _ = cexp (σ * t) * ∫ u, G u * ((Real.sin (η * (t - u)) / (Real.pi * (t - u)) : ℝ) : ℂ) := by
        rw [← integral_indicator measurableSet_Ioi]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [hGdef, Set.indicator]
        split_ifs <;> simp

/-- DLMF 2.4.4–2.4.5: let `c > 0` and let `Q` be analytic in `ℜz ≥ c` with the differentiable
expansion `Q(z) ∼ ∑ Γ((s+λ)/μ) aₛ z^{-(s+λ)/μ}` as `z → ∞` there (2.4.4; `λ, μ > 0`, principal
powers), the derivative having the termwise differentiated expansion. Then the inversion
integral 2.4.5 converges at each limit, its value `q(t)` is independent of `σ ∈ [c, ∞)`, and
`q(t) ∼ ∑ aₛ t^{(s+λ-μ)/μ}` as `t → 0⁺` (2.3.7). The improper integral is the limit of
`bromwichPartialIntegral`. -/
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
    ∃ q : ℝ → ℂ, (∀ σ, c ≤ σ → ∀ t, 0 < t →
        Tendsto (bromwichPartialIntegral Q σ t) atTop (𝓝 (q t))) ∧
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
    (hq : Tendsto (bromwichPartialIntegral Q σ t) atTop (𝓝 (q t)))
    (hf : Tendsto (bromwichPartialIntegral F σ t) atTop (𝓝 (f t))) :
    Tendsto (fun η : ℝ => (Real.exp (σ * t) / (2 * π) : ℂ) *
        ∫ τ in -η..η, Complex.exp (I * t * τ) * (Q (σ + τ * I) - F (σ + τ * I)))
      atTop (𝓝 (q t - f t)) := by
  refine (hq.sub hf).congr fun η => ?_
  unfold bromwichPartialIntegral
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

/-- Derivatives of a function holomorphic on `ℜz > c - 1` along the vertical line `ℜz = c`. -/
private lemma hasDerivAt_iteratedDeriv_line {Q : ℂ → ℂ} {c : ℝ}
    (hQ : DifferentiableOn ℂ Q {z | c - 1 < z.re}) (j : ℕ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => iteratedDeriv j Q (c + τ * I))
      (iteratedDeriv (j + 1) Q (c + τ * I) * I) τ := by
  have hU : IsOpen {z : ℂ | c - 1 < z.re} := isOpen_lt continuous_const continuous_re
  have hA : AnalyticAt ℂ (iteratedDeriv j Q) (c + (τ : ℂ) * I) := by
    rw [iteratedDeriv_eq_iterate]
    exact (hQ.analyticOnNhd hU).iterated_deriv j _ (by simp)
  have h1 : HasDerivAt (iteratedDeriv j Q) (iteratedDeriv (j + 1) Q (c + (τ : ℂ) * I))
      (c + (τ : ℂ) * I) := by
    rw [iteratedDeriv_succ]; exact hA.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun w : ℂ => (c : ℂ) + w * I) I (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).mul_const I).const_add (c : ℂ)
  exact (h1.comp (τ : ℂ) h2).comp_ofReal


/-- DLMF 2.4.9 (Haar's method), stronger than DLMF, which also assumes local integrability of the
derivative data along the line (automatic here, by holomorphy): if `Q` and `F` are holomorphic in
the half-plane `ℜz > c - 1` and their Fourier integrals along the vertical line `ℜz = c`, through
derivative order `m`, converge uniformly for all sufficiently large `t`, then
`q(t) = f(t) + o(t^{-m} e^{ct})`. Integration by parts gives
`t L_j(t) + L_{j+1}(t) = 0`, the boundary term changing sign under `t ↦ t + π/η`. -/
@[dlmf 2.4.E9]
theorem haar_isLittleO_pow' {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {c T : ℝ} {m : ℕ} {L : ℕ → ℝ → ℂ}
    (hQ : DifferentiableOn ℂ Q {z | c - 1 < z.re})
    (hF : DifferentiableOn ℂ F {z | c - 1 < z.re})
    (hunif : ∀ j ≤ m, TendstoUniformlyOn (fun (η t : ℝ) => ∫ τ in -η..η,
      Complex.exp (I * t * τ) * (iteratedDeriv j Q (c + τ * I) - iteratedDeriv j F (c + τ * I)))
      (L j) atTop (Ici T))
    (hqf : ∀ t, T ≤ t → q t - f t = (Real.exp (c * t) / (2 * π) : ℂ) * L 0 t) :
    (fun t => q t - f t) =o[atTop] fun t => (t : ℝ) ^ (-(m : ℝ)) * Real.exp (c * t) := by
  set D : ℕ → ℝ → ℂ := fun j τ => iteratedDeriv j Q (c + τ * I) - iteratedDeriv j F (c + τ * I)
    with hDdef
  have hD : ∀ j τ, HasDerivAt (D j) (D (j + 1) τ * I) τ := fun j τ => by
    have := (hasDerivAt_iteratedDeriv_line hQ j τ).sub (hasDerivAt_iteratedDeriv_line hF j τ)
    convert this using 1; simp only [hDdef, sub_mul]
  have hDc : ∀ j, Continuous (D j) := fun j =>
    continuous_iff_continuousAt.2 fun τ => (hD j τ).continuousAt
  set A : ℕ → ℝ → ℝ → ℂ := fun j η t => ∫ τ in -η..η, cexp (I * t * τ) * D j τ with hAdef
  have hAc : ∀ j η, Continuous (A j η) := fun j η => by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    have := hDc j
    fun_prop
  have hLc : ∀ j ≤ m, ContinuousOn (L j) (Ici T) := fun j hj =>
    (hunif j hj).continuousOn (Frequently.of_forall fun η => (hAc j η).continuousOn)
  -- integration by parts
  have hibp : ∀ j η t, I * t * A j η t + I * A (j + 1) η t =
      cexp (I * t * η) * D j η - cexp (I * t * ((-η : ℝ) : ℂ)) * D j (-η) := by
    intro j η t
    have hφ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => cexp (I * t * τ) * D j τ)
        (cexp (I * t * τ) * (I * t) * D j τ + cexp (I * t * τ) * (D (j + 1) τ * I)) τ := by
      intro τ
      have he : HasDerivAt (fun w : ℂ => cexp (I * t * w)) (cexp (I * t * τ) * (I * t)) τ := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul (I * t)).cexp
      exact he.comp_ofReal.mul (hD j τ)
    have hcont : Continuous fun τ : ℝ =>
        cexp (I * t * τ) * (I * t) * D j τ + cexp (I * t * τ) * (D (j + 1) τ * I) := by
      have := hDc j; have := hDc (j + 1); fun_prop
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hφ τ)
      (hcont.intervalIntegrable (-η) η)
    rw [← h, intervalIntegral.integral_add]
    · simp only [hAdef, ← intervalIntegral.integral_const_mul]
      congr 1 <;> refine intervalIntegral.integral_congr fun τ _ => ?_ <;> ring
    · have := hDc j; exact Continuous.intervalIntegrable (by fun_prop) _ _
    · have := hDc (j + 1); exact Continuous.intervalIntegrable (by fun_prop) _ _
  -- the boundary term changes sign under `t ↦ t + π/η`, so its limit vanishes
  have hkey : ∀ j < m, ∀ t, T ≤ t → t * L j t + L (j + 1) t = 0 := by
    intro j hj t ht
    have hj' : j ≤ m := hj.le
    have hj1 : j + 1 ≤ m := hj
    set X : ℂ := I * t * L j t + I * L (j + 1) t
    have h1 : Tendsto (fun η => I * t * A j η t + I * A (j + 1) η t) atTop (𝓝 X) :=
      (((hunif j hj').tendsto_at ht).const_mul _).add (((hunif _ hj1).tendsto_at ht).const_mul _)
    set s : ℝ → ℝ := fun η => t + π / η
    have hs0 : Tendsto s atTop (𝓝 t) := by
      have h0 : Tendsto (fun η : ℝ => π / η) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa [s] using (tendsto_const_nhds (x := t)).add h0
    have hs : Tendsto s atTop (𝓝[Ici T] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hs0, ?_⟩
      filter_upwards [eventually_gt_atTop 0] with η hη
      show T ≤ t + π / η
      have : 0 < π / η := by positivity
      linarith
    have hsr : Tendsto (fun η => (s η : ℂ)) atTop (𝓝 (t : ℂ)) :=
      (continuous_ofReal.tendsto _).comp hs0
    have h2 : Tendsto (fun η => I * (s η) * A j η (s η) + I * A (j + 1) η (s η)) atTop (𝓝 X) :=
      ((hsr.const_mul I).mul ((hunif j hj').tendsto_comp
          ((hLc j hj') t ht) hs)).add
        (((hunif _ hj1).tendsto_comp ((hLc _ hj1) t ht) hs).const_mul _)
    have h3 : Tendsto (fun η => -(I * t * A j η t + I * A (j + 1) η t)) atTop (𝓝 X) := by
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with η hη
      rw [hibp, hibp]
      have hη' : (η : ℂ) ≠ 0 := ofReal_ne_zero.2 hη.ne'
      have e1 : cexp (I * ((s η : ℝ) : ℂ) * η) = -cexp (I * t * η) := by
        rw [show I * ((s η : ℝ) : ℂ) * η = I * t * η + π * I by
          simp only [s]; push_cast; field_simp, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      have e2 : cexp (I * ((s η : ℝ) : ℂ) * ((-η : ℝ) : ℂ)) =
          -cexp (I * t * ((-η : ℝ) : ℂ)) := by
        rw [show I * ((s η : ℝ) : ℂ) * ((-η : ℝ) : ℂ) = I * t * ((-η : ℝ) : ℂ) + -(π * I) by
          simp only [s]; push_cast; field_simp; ring, Complex.exp_add, Complex.exp_neg,
          Complex.exp_pi_mul_I]
        ring
      rw [e1, e2]; ring
    have hX : X = -X := tendsto_nhds_unique h3 (by simpa using h1.neg)
    have hX0 : X = 0 := by linear_combination (1 / 2 : ℂ) * hX
    have : I * (t * L j t + L (j + 1) t) = 0 := by rw [← hX0]; ring
    simpa [I_ne_zero] using this
  -- iterate: `L₀(t) = (-1/t)^j L_j(t)`
  have hiter : ∀ j ≤ m, ∀ t, T ≤ t → 0 < t → L 0 t = (-(t : ℂ)⁻¹) ^ j * L j t := by
    intro j
    induction j with
    | zero => intro _ t _ _; simp
    | succ j ih =>
      intro hj t hT ht
      rw [ih (by omega) t hT ht]
      have hk := hkey j (by omega) t hT
      have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
      rw [show L j t = -(t : ℂ)⁻¹ * L (j + 1) t by field_simp; linear_combination hk, pow_succ]
      ring
  -- Riemann–Lebesgue for the `m`-th derivatives
  have hm := haar_isLittleO (q := fun t => (Real.exp (c * t) / (2 * π) : ℂ) * L m t)
    (f := fun _ => 0) (hunif m le_rfl) (fun t _ => by simp)
  simp only [sub_zero] at hm
  have hB : (fun t : ℝ => (-(t : ℂ)⁻¹) ^ m) =O[atTop] fun t : ℝ => t ^ (-(m : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_pow, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, Real.rpow_natCast,
      inv_pow]
  refine (hB.mul_isLittleO hm).congr' ?_ (Eventually.of_forall fun t => rfl)
  filter_upwards [eventually_ge_atTop T, eventually_gt_atTop 0] with t hT ht
  rw [hqf t hT, hiter m le_rfl t hT ht]
  ring

/-- DLMF 2.4.9 (Haar's method): if `Q` and `F` are holomorphic in the right half-plane
and their Fourier integrals along the vertical line, through derivative order `m`, converge
uniformly for all sufficiently large `t`, then `q(t) = f(t) + o(t^{-m} e^{ct})`.
Individual holomorphy identifies the separate derivative data with the derivatives of `Q-F`.
-/
@[dlmf 2.4.E9]
theorem haar_isLittleO_pow {Q F : ℂ → ℂ} {q f : ℝ → ℂ} {c T : ℝ} {m : ℕ} {L : ℕ → ℝ → ℂ}
    (_hd : ∀ j ≤ m, ∀ η : ℝ, IntervalIntegrable
      (fun τ : ℝ => iteratedDeriv j Q (c + τ * I) - iteratedDeriv j F (c + τ * I)) volume (-η) η)
    (hQ : DifferentiableOn ℂ Q {z | c - 1 < z.re})
    (hF : DifferentiableOn ℂ F {z | c - 1 < z.re})
    (hunif : ∀ j ≤ m, TendstoUniformlyOn (fun (η t : ℝ) => ∫ τ in -η..η,
      Complex.exp (I * t * τ) * (iteratedDeriv j Q (c + τ * I) - iteratedDeriv j F (c + τ * I)))
      (L j) atTop (Ici T))
    (hqf : ∀ t, T ≤ t → q t - f t = (Real.exp (c * t) / (2 * π) : ℂ) * L 0 t) :
    (fun t => q t - f t) =o[atTop] fun t => (t : ℝ) ^ (-(m : ℝ)) * Real.exp (c * t) :=
  haar_isLittleO_pow' hQ hF hunif hqf

end DLMF.AsymptoticApproximations
