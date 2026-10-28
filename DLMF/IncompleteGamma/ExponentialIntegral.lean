/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.SeriesRecurrences
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Generalized exponential integral, DLMF §8.19

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- Generalized exponential integral on the logarithmic plane. -/
def genExpIntEOnLog (p w : ℂ) : ℂ :=
  exp ((p-1)*w)*upperIncGammaOnLog (1-p) w

/-- Extension at zero in Re p>1; the old plain function keeps its totalized value. -/
def genExpIntEExtended (p z : ℂ) : ℂ :=
  if z=0 then 1/(p-1) else genExpIntE p z

/-- Horizontal-ray integral representation of the generalized exponential integral on the
principal slit plane. -/
@[dlmf 8.19.E2]
theorem genExpIntE_horizontal_integral (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(-p)*exp (-(z+t))) 0 (z^(1-p)*genExpIntE p z) := by
  have h := (upperIncGamma_horizontal_integral (1-p) hz).congr
    (g := fun t : ℝ => (z+t)^(-p)*exp (-(z+t))) fun t _ => by rw [show 1-p-1 = -p by ring]
  convert h using 1
  rw [genExpIntE, ← mul_assoc, ← cpow_add _ _ (slitPlane_ne_zero hz)]
  simp

/-- Laplace integral representation of the generalized exponential integral for arguments with
positive real part. -/
@[dlmf 8.19.E3]
theorem genExpIntE_laplace_complex (p : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genExpIntE p z=∫ t : ℝ in Ioi 1, exp (-z*t)*(t : ℂ)^(-p) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have hU := kummerU_laplace (a:=1) (b:=2-p) (z:=z) (by norm_num) hz
  simp only [Gamma_one, div_one, one_div_one, one_mul, sub_self, cpow_zero, mul_one,
    show (2-p:ℂ)-1-1 = -p by ring] at hU
  rw [genExpIntE_eq_exp_mul_kummerU p hz0, hU, ← integral_const_mul]
  have ht := setIntegral_Ioi_comp_add_right
    (fun s : ℝ => exp (-z*s)*(s:ℂ)^(-p)) 0 1
  simp only [zero_add] at ht
  rw [← ht]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  push_cast
  rw [show -z*((t:ℂ)+1) = -z + -z*t by ring, Complex.exp_add]
  rw [add_comm (1:ℂ) t]
  ring

/-- Stieltjes-type representation of the generalized exponential integral when both the order and
argument have positive real part. -/
@[dlmf 8.19.E4]
theorem genExpIntE_stieltjes {p z : ℂ} (hp : 0 < p.re) (hz : 0 < z.re) :
    genExpIntE p z=z^(p-1)*exp (-z)/Gamma p*(∫ t : ℝ in Ioi 0, (t : ℂ)^(p-1)*exp (-z*t)/(1+t)) := by
  rw [genExpIntE_eq_cpow_mul_kummerU, kummerU_laplace hp hz]
  have hI : (∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(p-1)*(1+(t:ℂ))^(p-p-1)) =
      ∫ t : ℝ in Ioi 0, (t : ℂ)^(p-1)*exp (-z*t)/(1+t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [sub_self, zero_sub, cpow_neg_one]
    rw [div_eq_mul_inv]
    ring
  rw [hI]
  ring

/-- `z log z → 0` as `z → 0`, `z ≠ 0`, in `ℂ`. -/
theorem tendsto_mul_log_nhdsNE_zero :
    Tendsto (fun z : ℂ => z * log z) (𝓝[≠] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hc : Tendsto (fun z : ℂ => |‖z‖ * Real.log ‖z‖| + π * ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Continuous (fun z : ℂ => |‖z‖ * Real.log ‖z‖| + π * ‖z‖) :=
      ((Real.continuous_mul_log.comp continuous_norm).abs).add (continuous_const.mul continuous_norm)
    simpa using (h1.tendsto 0).mono_left nhdsWithin_le_nhds
  refine squeeze_zero (fun _ => norm_nonneg _) (fun z => ?_) hc
  rw [norm_mul]
  calc ‖z‖ * ‖log z‖ ≤ ‖z‖ * (|Real.log ‖z‖| + π) := by
        gcongr
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [log_re, log_im]
        gcongr
        exact abs_arg_le_pi z
    _ = _ := by rw [abs_mul, abs_norm]; ring

/-- For orders with real part greater than one, the generalized exponential integral extends
continuously to zero with value `1/(p-1)`. -/
@[dlmf 8.19.E6]
theorem genExpIntEExtended_zero {p : ℂ} (hp : 1 < p.re) :
    genExpIntEExtended p 0=1/(p-1) ∧ ContinuousAt (genExpIntEExtended p) 0 := by
  have hval : genExpIntEExtended p 0 = 1/(p-1) := by simp [genExpIntEExtended]
  refine ⟨hval, ?_⟩
  have hp1 : p - 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hG : Gamma (1 - (2 - p)) / Gamma (1 - (2 - p) + 1) = 1/(p-1) := by
    have hG0 : Gamma (p - 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [show (1:ℂ) - (2 - p) = p - 1 by ring, Gamma_add_one _ hp1]
    field_simp
  have hU : Tendsto (fun z => kummerU 1 (2 - p) z) (𝓝[≠] 0) (𝓝 (1/(p-1))) := by
    rw [← hG, ← tendsto_sub_nhds_zero_iff]
    rw [show (1:ℂ) - (2 - p) + 1 = 1 - (2 - p) + 1 by ring]
    by_cases hb : (2 - p).re ≤ 0
    · by_cases hb0 : 2 - p = 0
      · have h := (isBigO_kummerU_at_zero_b_zero 1).trans_tendsto tendsto_mul_log_nhdsNE_zero
        rw [hb0]
        simpa using h
      · exact ((isBigO_kummerU_at_zero_re_nonpos 1 (2 - p) hb hb0).mono nhdsWithin_le_nhds).trans_tendsto
          ((continuous_id.tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds)
    · push Not at hb
      refine (isBigO_kummerU_at_zero_re_zero_to_one 1 (2 - p) hb (by simp; linarith)).trans_tendsto ?_
      have hr : 0 < ((1 - (2 - p).re : ℝ) : ℂ).re := by simp; linarith
      have hc := (continuousAt_cpow_zero_of_re_pos hr).tendsto.comp
        ((continuous_id.prodMk continuous_const).tendsto (0 : ℂ))
      have h0 : (0 : ℂ) ^ (((1 - (2 - p).re : ℝ) : ℂ)) = 0 :=
        zero_cpow (fun h => by rw [h] at hr; simp at hr)
      simp only [Function.comp_def, id] at hc
      rw [h0] at hc
      exact_mod_cast hc.mono_left nhdsWithin_le_nhds
  have hE : Tendsto (genExpIntEExtended p) (𝓝[≠] 0) (𝓝 (1/(p-1))) := by
    have he : Tendsto (fun z : ℂ => exp (-z)) (𝓝[≠] 0) (𝓝 1) := by
      simpa using (continuous_neg.cexp.tendsto 0).mono_left nhdsWithin_le_nhds
    refine ((he.mul hU).congr' ?_).trans (by rw [one_mul])
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := hz
    simp only [genExpIntEExtended, hz', ↓reduceIte, genExpIntE_eq_exp_mul_kummerU p hz']
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hval]
  exact hE

/-- At integral orders at least two, express the generalized exponential integral using `E₁` and a
finite factorial sum. -/
@[dlmf 8.19.E7]
theorem genExpIntE_nat_finite {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE n z=(-z)^(n-1)/(n-1).factorial*genExpIntE 1 z+exp (-z)/(n-1).factorial*(∑ k ∈ Finset.range (n-1), ((n-k-2).factorial : ℂ)*(-z)^k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n-2, by omega⟩
  have h := upperIncGamma_neg_nat_finite (m+1) hz
  rw [show m+2-1 = m+1 by omega, genExpIntE]
  push_cast
  rw [show (1:ℂ)-(m+2) = -((m:ℂ)+1) by ring, show (m:ℂ)+2-1 = ((m+1:ℕ):ℂ) by push_cast; ring,
    cpow_natCast]
  push_cast at h
  rw [h]
  have hsum : (∑ k ∈ Finset.range (m+1), ((m+2-k-2).factorial : ℂ)*(-z)^k) =
      ∑ k ∈ Finset.range (m+1), (-1:ℂ)^(m+k)*(k.factorial : ℂ)*z^(m-k) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m-k, by omega⟩
    rw [show k+j+1-1-k = j by omega, show k+j+2-j-2 = k by omega, show k+j-k = j by omega,
      neg_pow, pow_add]
    have hk2 : ((-1:ℂ)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination -(-1:ℂ)^j*(k.factorial:ℂ)*z^j*hk2
  have hterm : ∀ k ∈ Finset.range (m+1), z^(m+1)*((-1:ℂ)^(m+1)/((m+1).factorial : ℂ)*(exp (-z)*
      ((-1:ℂ)^k*(k.factorial:ℂ)/z^(k+1)))) =
      -(exp (-z)/((m+1).factorial : ℂ)*((-1:ℂ)^(m+k)*(k.factorial : ℂ)*z^(m-k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m-k, by omega⟩
    rw [show k+j-k = j by omega]
    have hzk : z^(k+1) ≠ 0 := pow_ne_zero _ hz
    rw [show k+j+1 = j+(k+1) by ring, pow_add z, pow_add (-1:ℂ) j (k+1),
      show k+j+k = j+2*k by ring, pow_add (-1:ℂ) j (2*k), pow_mul, neg_one_sq, one_pow]
    have hk2 : ((-1:ℂ)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    field_simp
    rw [pow_succ]
    linear_combination (-(k.factorial : ℂ) / ((j + (k + 1)).factorial : ℂ)) * hk2
  have hS : z^(m+1)*((-1:ℂ)^(m+1)/((m+1).factorial : ℂ)*(exp (-z)*
      ∑ k ∈ Finset.range (m+1), (-1:ℂ)^k*(k.factorial:ℂ)/z^(k+1))) =
      -(exp (-z)/((m+1).factorial : ℂ)*
        ∑ k ∈ Finset.range (m+1), (-1:ℂ)^(m+k)*(k.factorial : ℂ)*z^(m-k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hterm
  rw [hsum, neg_pow z]
  linear_combination -hS

/-- At positive integral order, the logarithmic digamma term and the omitted-index exponential
series give the generalized exponential integral. -/
@[dlmf 8.19.E8]
theorem genExpIntE_nat_hasSum {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => if k=n-1 then 0 else (-z)^k/((k.factorial : ℂ)*(1-(n : ℂ)+k))) ((-z)^(n-1)/(n-1).factorial*(digamma n-log z)-genExpIntE n z) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have h := upperIncGamma_neg_nat_hasSum m hz
  simp only [Nat.add_sub_cancel]
  convert h using 1
  · funext k
    push_cast
    rw [show 1-((m:ℂ)+1)+k = k - m by ring]
  · rw [genExpIntE, zpow_natCast, neg_pow]
    push_cast
    rw [show (m:ℂ)+1-1 = m by ring, show 1-((m:ℂ)+1) = -m by ring, cpow_natCast]
    ring

/-- `∑_{j=0}^{n} (-1)^j C(n+1, j+1) = 1`. -/
theorem incG_alt_choose_succ (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), ((n+1).choose (j+1) : ℚ) * (-1)^j = 1 := by
  have h := Int.alternating_sum_range_choose (n := n+1)
  simp only [Nat.add_one_ne_zero, ↓reduceIte] at h
  rw [Finset.sum_range_succ'] at h
  have h' : (∑ j ∈ Finset.range (n+1), ((-1:ℤ)^(j+1) * ((n+1).choose (j+1) : ℤ))) = -1 := by
    simp at h; linarith
  have h'' : (∑ j ∈ Finset.range (n+1), (((n+1).choose (j+1) : ℤ) * (-1)^j)) = 1 := by
    have : (∑ j ∈ Finset.range (n+1), ((-1:ℤ)^(j+1) * ((n+1).choose (j+1) : ℤ))) =
        -∑ j ∈ Finset.range (n+1), (((n+1).choose (j+1) : ℤ) * (-1)^j) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => by ring
    linarith
  exact_mod_cast h''

/-- `∑_{j=1}^{n} (-1)^{j-1} C(n,j)/j = H_n`. -/
theorem incG_sum_choose_harmonic (n : ℕ) :
    ∑ j ∈ Finset.range n, (n.choose (j+1) : ℚ) * (-1)^j / (j+1) = harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ, ← ih]
    have hsplit : ∀ j ∈ Finset.range (n+1), ((n+1).choose (j+1) : ℚ) * (-1)^j / (j+1) =
        (n.choose j : ℚ) * (-1)^j / (j+1) + (n.choose (j+1) : ℚ) * (-1)^j / (j+1) := by
      intro j _; rw [Nat.choose_succ_succ']; push_cast; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_range_succ (fun j =>
      (n.choose (j+1) : ℚ) * (-1)^j / (j+1)), Nat.choose_succ_self, Nat.cast_zero, zero_mul,
      zero_div, add_zero]
    have hB : ∑ j ∈ Finset.range (n+1), (n.choose j : ℚ) * (-1)^j / (j+1) = 1/(n+1) := by
      have hc : ∀ j ∈ Finset.range (n+1), (n.choose j : ℚ) * (-1)^j / (j+1) =
          ((n+1).choose (j+1) : ℚ) * (-1)^j / (n+1) := by
        intro j _
        have := Nat.add_one_mul_choose_eq n j
        have hq : ((n:ℚ)+1) * n.choose j = (n+1).choose (j+1) * ((j:ℚ)+1) := by exact_mod_cast this
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (-1:ℚ)^j * hq
      rw [Finset.sum_congr rfl hc, ← Finset.sum_div, incG_alt_choose_succ]
    rw [hB]; push_cast; ring

/-- The `E₁` part of DLMF 6.6.2 as a power series in `z`, with constant term `-γ`. -/
theorem incG_hasSum_E1_add_log {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => if k = 0 then -(Real.eulerMascheroniConstant : ℂ)
      else -(-z)^k/((k.factorial : ℂ)*k)) (genExpIntE 1 z + log z) := by
  have h := hasSum_Ein_complex z
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, ↓reduceIte, Nat.add_one_ne_zero]
  rw [expIntE1_eq_Ein_complex hz]
  convert h using 1
  · funext k; push_cast; rw [neg_pow z, pow_succ (-1:ℂ)]; ring
  · ring

/-- Identity under the stated parameter and domain assumptions: `(-(-z)^(j+1)/(((j+1).factorial :
ℂ)*((j+1:ℕ):ℂ))) * (z^(n-(j+1))/((n-(j+1)).factorial : ℂ)) = z^n/(n.factorial : ℂ) *
((n.choose (j+1) : ℂ) * (-1)^j / ((j:ℂ)+1))`. -/
theorem incG_digamma_conv_term {n j : ℕ} (hj : j < n) (z : ℂ) :
    (-(-z)^(j+1)/(((j+1).factorial : ℂ)*((j+1:ℕ):ℂ))) * (z^(n-(j+1))/((n-(j+1)).factorial : ℂ)) =
      z^n/(n.factorial : ℂ) * ((n.choose (j+1) : ℂ) * (-1)^j / ((j:ℂ)+1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = (j+1) + m := ⟨n-(j+1), by omega⟩
  have hc := Nat.choose_mul_factorial_mul_factorial (n := j+1+m) (k := j+1) (by omega)
  rw [show j+1+m-(j+1) = m by omega] at hc ⊢
  have hc' : ((j+1+m).choose (j+1) : ℂ) * ((j+1).factorial : ℂ) * (m.factorial : ℂ) =
      ((j+1+m).factorial : ℂ) := by exact_mod_cast hc
  rw [← hc', neg_pow z (j+1), pow_succ (-1:ℂ) j, pow_add z (j+1) m]
  have h1 : ((j+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : ((j:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have h4 : ((j+1+m).choose (j+1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  push_cast
  field_simp

/-- DLMF 6.6.3: `∑ z^k ψ(k+1)/k! = e^z (E₁(z) + ln z)`, by a Cauchy product with 6.6.2. -/
theorem incG_expIntE1_digamma_series {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^k/(k.factorial : ℂ)*digamma (k+1)) (exp z*(genExpIntE 1 z+log z)) := by
  set g : ℕ → ℂ := fun k => if k = 0 then -(Real.eulerMascheroniConstant : ℂ)
      else -(-z)^k/((k.factorial : ℂ)*k) with hgdef
  set e : ℕ → ℂ := fun k => z^k/(k.factorial : ℂ) with hedef
  have hg := incG_hasSum_E1_add_log hz
  have he : HasSum e (exp z) := by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp z
  have hen : Summable fun k => ‖e k‖ := by
    refine (Real.summable_pow_div_factorial ‖z‖).congr fun k => ?_
    simp [e, norm_pow]
  have hgn : Summable fun k => ‖g k‖ := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial ‖z‖))
    simp only [g, Nat.add_one_ne_zero, ↓reduceIte, norm_neg, norm_div, norm_pow, norm_mul,
      Complex.norm_natCast]
    have hf : (0:ℝ) < ((k+1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_div_iff₀ (by positivity) hf]
    have : (1:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast Nat.le_add_left 1 k
    have h5 := mul_le_mul_of_nonneg_left this
      (mul_nonneg (pow_nonneg (norm_nonneg z) (k+1)) hf.le)
    linarith
  have hC := hasSum_sum_range_mul_of_summable_norm hgn hen
  rw [hg.tsum_eq, he.tsum_eq, mul_comm] at hC
  convert hC using 1
  funext n
  rw [Finset.sum_range_succ']
  have hterm : ∀ j ∈ Finset.range n, g (j+1) * e (n-(j+1)) =
      z^n/(n.factorial : ℂ) * ((n.choose (j+1) : ℂ) * (-1)^j / ((j:ℂ)+1)) := by
    intro j hj
    simp only [g, e, Nat.add_one_ne_zero, ↓reduceIte]
    exact incG_digamma_conv_term (Finset.mem_range.mp hj) z
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hH := congrArg (Rat.cast : ℚ → ℂ) (incG_sum_choose_harmonic n)
  push_cast at hH
  rw [hH]
  simp only [g, e, ↓reduceIte, Nat.sub_zero]
  rw [show ((n:ℂ)+1) = ((n:ℕ):ℂ)+1 from rfl, Complex.digamma_nat_add_one]
  ring

/-- Factorial form of DLMF 8.19.9, by induction through 8.19.12. -/
theorem incG_genExpIntE_succ_digamma (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE ((m:ℂ)+1) z = (-1:ℂ)^(m+1)*z^m/(m.factorial : ℂ)*log z +
      exp (-z)/(m.factorial : ℂ)*(∑ k ∈ Finset.range m, (-z)^k*((m-(k+1)).factorial : ℂ)) +
      exp (-z)*(-z)^m/(m.factorial : ℂ)*(∑' k : ℕ, z^k/(k.factorial : ℂ)*digamma (k+1)) := by
  have hS := (incG_expIntE1_digamma_series hz).tsum_eq
  rw [hS]
  induction m with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, mul_one]
    have he : exp (-z) * exp z = 1 := by rw [← Complex.exp_add]; simp
    linear_combination (-(genExpIntE 1 z + log z)) * he
  | succ m ih =>
    have hr := genExpIntE_add_one ((m:ℂ)+1) hz
    rw [ih] at hr
    have hm : (m:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    rw [Finset.sum_range_succ']
    have hsum : ∑ k ∈ Finset.range m, (-z)^(k+1)*((m+1-(k+1+1)).factorial : ℂ) =
        -z * ∑ k ∈ Finset.range m, (-z)^k*((m-(k+1)).factorial : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show m+1-(k+1+1) = m-(k+1) by omega]; ring
    rw [hsum, show m+1-(0+1) = m by omega, Nat.factorial_succ]
    push_cast
    apply mul_left_cancel₀ hm
    rw [show ((m:ℂ)+1+1) = ((m:ℂ)+1)+1 from rfl]
    have hr' : ((m:ℂ)+1) * genExpIntE ((m:ℂ)+1+1) z = exp (-z) - z * ((-1:ℂ)^(m+1)*z^m/(m.factorial : ℂ)*log z +
      exp (-z)/(m.factorial : ℂ)*(∑ k ∈ Finset.range m, (-z)^k*((m-(k+1)).factorial : ℂ)) +
      exp (-z)*(-z)^m/(m.factorial : ℂ)*(exp z*(genExpIntE 1 z+log z))) := by
      linear_combination hr
    rw [hr']
    field_simp
    ring

/-- The digamma-series representation of the generalized exponential integral at positive integral
order and nonzero argument. -/
theorem incG_genExpIntE_nat_digamma_series {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE n z=(-1 : ℂ)^n*z^(n-1)/(n-1).factorial*log z+exp (-z)/(n-1).factorial*(∑ k ∈ Finset.range (n-1), (-z)^k*Gamma (n-(k+1)))+exp (-z)*(-z)^(n-1)/(n-1).factorial*(∑' k : ℕ, z^k/(k.factorial : ℂ)*digamma (k+1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hG : ∀ k ∈ Finset.range m, (-z)^k*Gamma (((m+1:ℕ):ℂ)-(k+1)) =
      (-z)^k*((m-(k+1)).factorial : ℂ) := by
    intro k hk
    have hk' : k+1 ≤ m := Finset.mem_range.mp hk
    rw [show ((m+1:ℕ):ℂ)-(k+1) = ((m-(k+1) : ℕ) : ℂ)+1 by push_cast [Nat.cast_sub hk']; ring,
      Complex.Gamma_nat_eq_factorial]
  rw [Finset.sum_congr rfl hG, show ((m+1:ℕ):ℂ) = (m:ℂ)+1 by push_cast; rfl,
    incG_genExpIntE_succ_digamma m hz]

/-- The digamma-series representation of the generalized exponential integral at positive integral
order and nonzero argument. -/
@[dlmf 8.19.E9]
theorem genExpIntE_nat_digamma_series {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE n z=(-1 : ℂ)^n*z^(n-1)/(n-1).factorial*log z+exp (-z)/(n-1).factorial*(∑ k ∈ Finset.range (n-1), (-z)^k*Gamma (n-(k+1)))+exp (-z)*(-z)^(n-1)/(n-1).factorial*(∑' k : ℕ, z^k/(k.factorial : ℂ)*digamma (k+1)) :=
  incG_genExpIntE_nat_digamma_series hn hz

/-- Excluding positive integral `p` excludes nonpositive integral `1-p`. -/
theorem one_sub_ne_neg_nat {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) : ∀ n : ℕ, 1-p ≠ -n :=
  fun n h => hp n (by linear_combination -h)

/-- Power-series representation away from positive integral orders, with the singular power
term separated using Gamma. -/
@[dlmf 8.19.E10]
theorem genExpIntE_hasSum_noninteger {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-z)^k/((k.factorial : ℂ)*(1-p+k))) (z^(p-1)*Gamma (1-p)-genExpIntE p z) := by
  have h := (upperIncGamma_hasSum_alternating (one_sub_ne_neg_nat hp) hz).mul_left (z^(p-1))
  rw [genExpIntE, ← mul_sub]
  refine h.congr_fun fun k => ?_
  rw [cpow_add _ _ hz, cpow_natCast, neg_pow]
  have hp1 : z^(p-1)*z^(1-p) = 1 := by rw [← cpow_add _ _ hz]; simp
  linear_combination -(-1:ℂ)^k*z^k/((k.factorial : ℂ)*(1-p+k)) * hp1

/-- Reciprocal-Gamma exponential series for the generalized exponential integral, away from
positive integral order parameters. -/
@[dlmf 8.19.E11]
theorem genExpIntE_hasSum_exponential {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => exp (-z)*z^k/Gamma (2-p+k)) (z^(p-1)-genExpIntE p z/Gamma (1-p)) := by
  have ha := one_sub_ne_neg_nat hp
  have h := scIncGamma_hasSum_exponential (1-p) z
  rw [scIncGamma_eq ha hz] at h
  convert h using 1
  · funext k; congr 2; ring
  · have hc := lowerIncGamma_add_upperIncGamma ha hz
    rw [genExpIntE, show -(1-p) = p-1 by ring]
    field_simp [Gamma_ne_zero ha]
    linear_combination -z^(p-1)*hc

/-- The required limiting interpretation at positive integral p. -/
@[dlmf 8.19.E10, dlmf 8.19.E11]
theorem genExpIntE_series_integer_limits {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun p : ℂ => z^(p-1)*Gamma (1-p)-∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(1-p+k))) (𝓝[≠] (n : ℂ)) (𝓝 (genExpIntE n z)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have hcont : Continuous fun p : ℂ => genExpIntE p z :=
    ((continuous_const_cpow' hz).comp (continuous_id.sub continuous_const)).mul
      ((upperIncGamma_parameter_entire hz).continuous.comp (continuous_const.sub continuous_id))
  have hmap : Tendsto (fun p : ℂ => 1-p) (𝓝[≠] ((m+1:ℕ) : ℂ)) (𝓝[≠] (-(m:ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun p : ℂ => 1-p) (𝓝 ((m+1:ℕ) : ℂ)) (𝓝 (1-((m+1:ℕ) : ℂ))) :=
        (continuous_const.sub continuous_id).tendsto _
      convert h.mono_left nhdsWithin_le_nhds using 2; push_cast; ring
    · filter_upwards [self_mem_nhdsWithin] with p hp
      simp only [mem_compl_iff, mem_singleton_iff] at hp ⊢
      intro h
      apply hp
      push_cast
      linear_combination -h
  have hev := hmap.eventually (eventually_nhdsNE_neg_nat_ne m)
  refine ((hcont.tendsto _).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev] with p hp
  have hp' : ∀ k : ℕ, p ≠ k+1 := fun k h => hp k (by rw [h]; ring)
  rw [(genExpIntE_hasSum_noninteger hp' hz).tsum_eq]
  ring

/-- First-order differential equation for the exponentially scaled generalized exponential
integral on the principal slit plane. -/
@[dlmf 8.19.E14]
theorem genExpIntE_scaled_derivative (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun t => exp t*genExpIntE p t) (exp z*genExpIntE p z*(1+(p-1)/z)-1/z) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := ((hasDerivAt_id z).cexp).mul (hasDerivAt_genExpIntE p hz)
  have hr := genExpIntE_add_one (p-1) hz0
  rw [sub_add_cancel] at hr
  simp only [id_eq] at h
  refine h.congr_deriv ?_
  have he := Complex.exp_add z (-z)
  simp only [add_neg_cancel, Complex.exp_zero] at he
  field_simp
  linear_combination -exp z * hr + he

/-- `t^s e^{-bt}` is integrable on `(1,∞)` for `b > 0`. -/
theorem incG_integrableOn_rpow_mul_exp_neg {s b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t^s * Real.exp (-b*t)) (Ioi 1) := by
  refine integrable_of_isBigO_exp_neg (b := b/2) (by positivity) ?_ ?_
  · intro t ht
    have ht0 : (0:ℝ) < t := by have : (1:ℝ) ≤ t := ht; linarith
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id))).continuousWithinAt
  · have h := (isLittleO_rpow_exp_pos_mul_atTop s (b := b/2) (by positivity)).isBigO.mul
      (isBigO_refl (fun t : ℝ => Real.exp (-b*t)) atTop)
    refine h.congr' (Eventually.of_forall fun t => rfl) (Eventually.of_forall fun t => ?_)
    simp only
    rw [← Real.exp_add]; ring_nf

/-- The integrand of the `j`-th parameter derivative. -/
theorem incG_norm_paramIntegrand_le (j : ℕ) (q z : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖(Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t)‖ ≤ t^((j:ℝ) - q.re) * Real.exp (-z.re*t) := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlt : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0,
    Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp]
  have hre : (-z*(t:ℂ)).re = -z.re*t := by simp
  rw [hre, Real.rpow_sub ht0, Real.rpow_natCast, neg_re, Real.rpow_neg ht0.le, div_eq_mul_inv]
  have : Real.log t ^ j ≤ t^j := pow_le_pow_left₀ hl0 hlt j
  gcongr

/-- The function `(fun t : ℝ => (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t))` is continuous on
`(Ioi 0)`. -/
theorem incG_paramIntegrand_continuousOn (j : ℕ) (q z : ℂ) :
    ContinuousOn (fun t : ℝ => (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t)) (Ioi 0) := by
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  refine ((continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht0.ne')).pow j).mul ?_ |>.mul ?_
  · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne'))
  · exact (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)).continuousAt

/-- The kernel `(fun t : ℝ => (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t))` is integrable on `(Ioi
1)`. -/
theorem incG_paramIntegrand_integrableOn (j : ℕ) (q : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t)) (Ioi 1) := by
  refine Integrable.mono' (incG_integrableOn_rpow_mul_exp_neg (s := (j:ℝ) - q.re) hz) ?_ ?_
  · exact ((incG_paramIntegrand_continuousOn j q z).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact incG_norm_paramIntegrand_le j q z (le_of_lt ht)

/-- At `q`, the function `(fun q => (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t))` has derivative
`(-((Real.log t : ℂ)^(j+1)*(t : ℂ)^(-q)*exp (-z*t)))`. -/
theorem incG_hasDerivAt_paramIntegrand (j : ℕ) (q z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun q => (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t))
      (-((Real.log t : ℂ)^(j+1)*(t : ℂ)^(-q)*exp (-z*t))) q := by
  have h := ((hasDerivAt_neg q).const_cpow (c := (t:ℂ)) (Or.inl (ofReal_ne_zero.mpr ht.ne')))
  have h2 := (h.const_mul ((Real.log t : ℂ)^j)).mul_const (exp (-z*t))
  convert h2 using 1
  rw [← ofReal_log ht.le]; ring

/-- Differentiation under the integral sign in the order parameter. -/
theorem incG_hasDerivAt_paramIntegral (j : ℕ) (q : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun q => ∫ t : ℝ in Ioi 1, (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t))
      (-(∫ t : ℝ in Ioi 1, (Real.log t : ℂ)^(j+1)*(t : ℂ)^(-q)*exp (-z*t))) q := by
  have hb := incG_integrableOn_rpow_mul_exp_neg (s := ((j+1:ℕ):ℝ) + (1 - q.re)) hz
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (1:ℝ)))
    (x₀ := q) (s := Metric.ball q 1) (bound := fun t : ℝ => t^(((j+1:ℕ):ℝ) + (1 - q.re)) * Real.exp (-z.re*t))
    (F := fun q (t:ℝ) => (Real.log t : ℂ)^j*(t : ℂ)^(-q)*exp (-z*t))
    (F' := fun q (t:ℝ) => -((Real.log t : ℂ)^(j+1)*(t : ℂ)^(-q)*exp (-z*t)))
    (Metric.ball_mem_nhds q one_pos)
    (Eventually.of_forall fun q' => (incG_paramIntegrand_integrableOn j q' hz).aestronglyMeasurable)
    (incG_paramIntegrand_integrableOn j q hz)
    ((incG_paramIntegrand_integrableOn (j+1) q hz).neg.aestronglyMeasurable)
    ?_ hb ?_
  · rw [integral_neg] at h; exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht q' hq'
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht
    rw [norm_neg]
    refine (incG_norm_paramIntegrand_le (j+1) q' z ht1).trans ?_
    gcongr
    · have := (abs_re_le_norm (q' - q)).trans_lt (Metric.mem_ball.mp hq' |> fun h => by
        rwa [dist_eq_norm] at h)
      rw [sub_re, abs_lt] at this
      push_cast; linarith [this.1]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht q' _
    exact incG_hasDerivAt_paramIntegrand j q' z (zero_lt_one.trans ht)

/-- Differentiating with respect to the order inserts powers of the logarithm into the Laplace
integral, with sign `(-1)^j`. -/
theorem incG_genExpIntE_parameter_derivatives (j : ℕ) (p : ℂ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv j (fun q => genExpIntE q z) p=(-1 : ℂ)^j*(∫ t : ℝ in Ioi 1, (Real.log t : ℂ)^j*(t : ℂ)^(-p)*exp (-z*t)) := by
  have h0 : (fun q => genExpIntE q z) = fun q => ∫ t : ℝ in Ioi 1, (Real.log t : ℂ)^0*(t : ℂ)^(-q)*exp (-z*t) := by
    funext q; rw [genExpIntE_laplace_complex q hz]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [h0]
  revert p
  induction j with
  | zero => intro p; simp
  | succ j ih =>
    intro p
    rw [iteratedDeriv_succ, show iteratedDeriv j _ = _ from funext ih]
    rw [((incG_hasDerivAt_paramIntegral j p hz).const_mul ((-1:ℂ)^j)).deriv]
    ring

/-- Differentiating with respect to the order inserts powers of the logarithm into the Laplace
integral, with sign `(-1)^j`. -/
@[dlmf 8.19.E15]
theorem genExpIntE_parameter_derivatives (j : ℕ) (p : ℂ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv j (fun q => genExpIntE q z) p=(-1 : ℂ)^j*(∫ t : ℝ in Ioi 1, (Real.log t : ℂ)^j*(t : ℂ)^(-p)*exp (-z*t)) :=
  incG_genExpIntE_parameter_derivatives j p hz

/-- Continued-fraction representation of the generalized exponential integral on the principal
slit plane, with alternating order and argument coefficients. -/
@[dlmf 8.19.E17]
theorem genExpIntE_continuedFraction (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasContinuedFraction (fun k => if k=0 then exp (-z) else if Odd k then p+((k-1)/2 : ℕ) else ((k/2 : ℕ) : ℂ)) (fun k => if Even k then z else 1) (genExpIntE p z) := by
  sorry

/-- Monodromy of the generalized exponential integral at nonintegral order under an integral
number of turns in the logarithmic argument. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_monodromy {p : ℂ} (hp : ∀ n : ℤ, p ≠ n) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog p (w+2*m*π*I)=2*π*I*exp (m*p*π*I)/Gamma p*sin (m*p*π)/sin (p*π)*exp ((p-1)*w)+genExpIntEOnLog p w := by
  have ha : ∀ n : ℕ, 1-p ≠ -n := fun n h => hp (n+1) (by push_cast; linear_combination -h)
  have hp0 : ∀ n : ℕ, p ≠ -n := fun n h => hp (-n) (by rw [h]; push_cast; ring)
  have hs : Complex.sin (p*π) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact hp k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk)
  have hG := Gamma_ne_zero hp0
  have hr := Complex.Gamma_mul_Gamma_one_sub p
  rw [mul_comm (π:ℂ) p] at hr
  unfold genExpIntEOnLog
  rw [show w+2*m*π*I=w+2*π*m*I by ring, upperIncGammaOnLog_monodromy w m ha]
  have e1 : exp ((p-1)*(w+2*π*m*I))*exp (2*π*m*I*(1-p))=exp ((p-1)*w) := by
    rw [← Complex.exp_add, show (p-1)*(w+2*π*m*I)+2*π*m*I*(1-p)=(p-1)*w by ring]
  have e2 : exp ((p-1)*(w+2*π*m*I))=exp (m*p*π*I)*exp (m*p*π*I)*exp ((p-1)*w) := by
    have := exp_add_two_pi_int_mul_I ((p-1)*w+2*m*p*π*I) (-m)
    rw [← Complex.exp_add, ← Complex.exp_add,
      show m*p*π*I+m*p*π*I+(p-1)*w=(p-1)*w+2*m*p*π*I by ring, ← this]; congr 1; push_cast; ring
  have e3 : exp (m*p*π*I)*exp (2*π*m*I*(1-p))=exp (-(m*p*π*I)) := by
    rw [← Complex.exp_add]
    have := exp_add_two_pi_int_mul_I (-(m*p*π*I)) m
    rw [← this]; congr 1; ring
  have hsin : Complex.sin (m*p*π)*(2*I)=exp (m*p*π*I)-exp (-(m*p*π*I)) := by
    rw [Complex.sin]; ring_nf; rw [I_sq]; ring
  rw [mul_add, ← mul_assoc, e1]
  have hG1 : Gamma (1-p)=π/(Complex.sin (p*π)*Gamma p) := by
    rw [eq_div_iff (mul_ne_zero hs hG)]; rw [eq_div_iff hs] at hr; linear_combination hr
  rw [hG1]
  rw [e2]
  linear_combination exp (m*p*π*I)*exp ((p-1)*w)*π*(Complex.sin (p*π)*Gamma p)⁻¹*(-e3-hsin)

/-- At positive integral order, a full turn in the logarithmic argument adds the explicit
exponential monodromy term. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_nat_monodromy {n : ℕ} (hn : 1 ≤ n) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog n (w+2*m*π*I)=genExpIntEOnLog n w+2*π*I*m*(-1 : ℂ)^n/(n-1).factorial*exp (((n : ℂ)-1)*w) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  unfold genExpIntEOnLog
  have h1 : (1:ℂ)-((k+1:ℕ):ℂ) = -(k:ℂ) := by push_cast; ring
  have he : exp ((((k+1:ℕ):ℂ)-1)*(w+2*m*π*I))=exp ((((k+1:ℕ):ℂ)-1)*w) := by
    have := exp_add_two_pi_int_mul_I ((((k+1:ℕ):ℂ)-1)*w) (k*m)
    rw [← this]; congr 1; push_cast; ring
  rw [h1, he, show w+2*m*π*I=w+2*π*m*I by ring, upperIncGammaOnLog_neg_nat_monodromy,
    show k+1-1=k by omega, pow_succ]
  ring

/-- At nonpositive integral order, the generalized exponential integral is unchanged by full turns
in the logarithmic argument. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_nonpos_nat_monodromy (n : ℕ) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog (-n) (w+2*m*π*I)=genExpIntEOnLog (-n) w := by
  unfold genExpIntEOnLog
  have ha : ∀ k : ℕ, 1-(-(n:ℂ)) ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have he : exp ((-(n:ℂ)-1)*(w+2*m*π*I))=exp ((-(n:ℂ)-1)*w) := by
    have := exp_add_two_pi_int_mul_I ((-(n:ℂ)-1)*w) (-(n+1)*m)
    rw [← this]; congr 1; push_cast; ring
  have he2 : exp (2*π*m*I*(1-(-(n:ℂ))))=1 := by
    have := exp_add_two_pi_int_mul_I 0 ((n+1)*m)
    rw [Complex.exp_zero] at this
    rw [show 2*π*m*I*(1-(-(n:ℂ)))=0+2*π*(((n+1)*m : ℤ):ℂ)*I by push_cast; ring]; exact this
  rw [he, show w+2*m*π*I=w+2*π*m*I by ring, upperIncGammaOnLog_monodromy w m ha, he2]
  ring

/-- Each nonzero-argument branch is entire in p. -/
theorem genExpIntEOnLog_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun p => genExpIntEOnLog p w) := by
  unfold genExpIntEOnLog
  have h := (upperIncGammaOnLog_parameter_entire w).comp (differentiable_const (1:ℂ) |>.sub differentiable_id)
  exact (by fun_prop : Differentiable ℂ fun p : ℂ => exp ((p-1)*w)).mul (by simpa [Function.comp_def] using h)

/-- Nontrivial monodromy except at nonpositive integral order. -/
theorem genExpIntEOnLog_branch_point {p : ℂ} (hp : ∀ n : ℕ, p ≠ -n) (w : ℂ) :
    genExpIntEOnLog p (w+2*π*I) ≠ genExpIntEOnLog p w := by
  by_cases hz : ∀ n : ℤ, p ≠ n
  · have h := genExpIntEOnLog_monodromy hz w 1
    have hs : Complex.sin (p*π) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k hk
      exact hz k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk)
    push_cast at h
    simp only [one_mul, mul_one] at h
    rw [h]
    intro h'
    have h0 := add_eq_right.mp h'
    rw [mul_div_assoc, div_self hs, mul_one] at h0
    simp [Gamma_ne_zero hp, Real.pi_ne_zero, I_ne_zero, Complex.exp_ne_zero] at h0
  · push Not at hz
    obtain ⟨n, rfl⟩ := hz
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k+1 := by
      rcases Int.eq_nat_or_neg n with ⟨j, rfl | rfl⟩
      · rcases j with _ | j
        · exact absurd (by simp) (hp 0)
        · exact ⟨j, by push_cast; ring⟩
      · exact absurd (by push_cast; ring) (hp j)
    subst hk
    have h := genExpIntEOnLog_nat_monodromy (n := k+1) (by omega) w 1
    push_cast at h ⊢
    simp only [mul_one] at h
    rw [h]
    intro h'
    have h0 := add_eq_left.mp h'
    simp [Real.pi_ne_zero, I_ne_zero, Complex.exp_ne_zero, Nat.factorial_ne_zero] at h0

/-- Real form of `E_p(x) = ∫₁^∞ e^{-xt} t^{-p} dt` for real `p` and `x > 0`. -/
theorem incG_genExpIntE_re_eq (p : ℝ) {x : ℝ} (hx : 0 < x) :
    (genExpIntE p x).re = ∫ t in Ioi 1, Real.exp (-x*t)*t^(-p) := by
  rw [genExpIntE_eq_integral (p:ℂ) hx]
  have : (∫ t in Ioi (1:ℝ), Real.exp (-x * t) • (t : ℂ) ^ (-(p:ℂ))) =
      ((∫ t in Ioi 1, Real.exp (-x*t)*t^(-p) : ℝ) : ℂ) := by
    rw [show ((∫ t in Ioi 1, Real.exp (-x*t)*t^(-p) : ℝ) : ℂ) =
      ∫ t in Ioi (1:ℝ), ((Real.exp (-x*t)*t^(-p) : ℝ) : ℂ) from integral_ofReal.symm]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
    rw [Complex.real_smul, ofReal_mul, ofReal_cpow ht0]; push_cast; ring_nf
  rw [this, ofReal_re]

/-- Integrability of `e^{-xt} t^{-p}` on `(1,∞)` for `p ≥ 0`, `x > 0`. -/
theorem incG_integrableOn_expInt {p : ℝ} (hp : 0 ≤ p) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x*t)*t^(-p)) (Ioi 1) := by
  refine (exp_neg_integrableOn_Ioi 1 hx).mono' ?_ ?_
  · exact (ContinuousOn.mul (by fun_prop) (fun t ht => (Real.continuousAt_rpow_const _ _
      (Or.inl (lt_trans one_pos ht).ne')).continuousWithinAt)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : t^(-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt ht) (by linarith)
    calc Real.exp (-x*t)*t^(-p) ≤ Real.exp (-x*t)*1 := by gcongr
      _ = _ := mul_one _

/-- Positivity of an integral over `(1,∞)` of a function positive on `(c,∞)`. -/
theorem incG_setIntegral_Ioi_one_pos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 1))
    (h0 : ∀ t ∈ Ioi (1:ℝ), 0 ≤ f t) {c : ℝ} (hc : ∀ t, c < t → 1 < t → 0 < f t) :
    0 < ∫ t in Ioi 1, f t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall h0)) hf]
  have hs : Ioi (max 1 c) ⊆ Function.support f ∩ Ioi 1 := fun t ht => by
    have h1 : 1 < t := lt_of_le_of_lt (le_max_left _ _) ht
    exact ⟨(hc t (lt_of_le_of_lt (le_max_right _ _) ht) h1).ne', h1⟩
  exact lt_of_lt_of_le (by simp) (measure_mono hs)

/-- Strict decrease of `E_p(x)` in real `p ≥ 0`. -/
theorem incG_genExpIntE_re_strictAnti {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) {x : ℝ} (hx : 0 < x) :
    (genExpIntE q x).re < (genExpIntE p x).re := by
  rw [incG_genExpIntE_re_eq p hx, incG_genExpIntE_re_eq q hx, ← sub_pos,
    ← integral_sub (incG_integrableOn_expInt hp hx) (incG_integrableOn_expInt (by linarith) hx)]
  refine incG_setIntegral_Ioi_one_pos ((incG_integrableOn_expInt hp hx).sub
    (incG_integrableOn_expInt (by linarith) hx)) (fun t ht => ?_) (c := 1) fun t _ ht => ?_
  · have := Real.rpow_le_rpow_of_exponent_le (le_of_lt ht) (show -q ≤ -p by linarith)
    nlinarith [Real.exp_pos (-x*t)]
  · have := Real.rpow_lt_rpow_of_exponent_lt ht (show -q < -p by linarith)
    nlinarith [Real.exp_pos (-x*t)]

/-- Real form of the recurrence `n E_{n+1}(x) + x E_n(x) = e^{-x}`. -/
theorem incG_genExpIntE_re_rec (p : ℝ) {x : ℝ} (hx : 0 < x) :
    p*(genExpIntE (p+1) x).re + x*(genExpIntE p x).re = Real.exp (-x) := by
  have h := congrArg Complex.re (genExpIntE_add_one (p:ℂ) (ofReal_ne_zero.mpr hx.ne'))
  rw [← ofReal_neg, ← ofReal_exp, ofReal_re] at h
  rw [← h]; simp [Complex.mul_re]

/-- `(x+n-1) E_n(x) < e^{-x}` for `n ≥ 1`. -/
theorem incG_genExpIntE_upper {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (x+n-1)*(genExpIntE n x).re < Real.exp (-x) := by
  have hr := incG_genExpIntE_re_rec ((n:ℝ)-1) hx
  rw [show (((n:ℝ)-1 : ℝ):ℂ)+1 = (n:ℂ) by push_cast; ring] at hr
  have hm := incG_genExpIntE_re_strictAnti (p := (n:ℝ)-1) (q := n)
    (by have : (1:ℝ) ≤ n := by exact_mod_cast hn
        linarith) (by linarith) hx
  push_cast at hr hm
  nlinarith

/-- DLMF 8.19.21 for natural order. -/
theorem incG_genExpIntE_rational_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    1/(x+n) < Real.exp x*(genExpIntE n x).re ∧ Real.exp x*(genExpIntE n x).re ≤ 1/(x+n-1) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hu := incG_genExpIntE_upper hn hx
  have hr := incG_genExpIntE_re_rec (n:ℝ) hx
  have hm := incG_genExpIntE_re_strictAnti (p := n) (q := n+1) (by linarith) (by linarith) hx
  push_cast at hr hm
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hex := Real.exp_pos x
  have hn0 : (0:ℝ) < n := by linarith
  have h1 : Real.exp (-x) < (x+n)*(genExpIntE n x).re := by
    nlinarith [mul_lt_mul_of_pos_left hm hn0]
  constructor
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_lt_mul_of_pos_left h1 hex]
  · rw [le_div_iff₀ (by linarith)]
    nlinarith

/-- DLMF 8.19.19 for natural order. -/
theorem incG_genExpIntE_order_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ((n : ℝ)-1)/n*(genExpIntE n x).re < (genExpIntE (n+1) x).re ∧ (genExpIntE (n+1) x).re < (genExpIntE n x).re := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hu := incG_genExpIntE_upper hn hx
  have hr := incG_genExpIntE_re_rec (n:ℝ) hx
  have hm := incG_genExpIntE_re_strictAnti (p := n) (q := n+1) (by linarith) (by linarith) hx
  push_cast at hr hm ⊢
  refine ⟨?_, hm⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

/-- Positivity of `E_p(x)` for real `p ≥ 0`, `x > 0`. -/
theorem incG_genExpIntE_re_pos {p : ℝ} (hp : 0 ≤ p) {x : ℝ} (hx : 0 < x) :
    0 < (genExpIntE p x).re := by
  rw [incG_genExpIntE_re_eq p hx]
  exact incG_setIntegral_Ioi_one_pos (incG_integrableOn_expInt hp hx)
    (fun t ht => by have := lt_trans one_pos (show (1:ℝ) < t from ht); positivity) (c := 1)
    fun t _ ht => by have := lt_trans one_pos ht; positivity

/-- Strict log-convexity `E_p² < E_{p-1} E_{p+1}` in real `p ≥ 1`. -/
theorem incG_genExpIntE_logconvex_real {p : ℝ} (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) :
    (genExpIntE (p:ℂ) x).re^2 < (genExpIntE ((p-1:ℝ):ℂ) x).re*(genExpIntE ((p+1:ℝ):ℂ) x).re := by
  set A := (genExpIntE ((p-1:ℝ):ℂ) x).re
  set B := (genExpIntE (p:ℂ) x).re
  set C := (genExpIntE ((p+1:ℝ):ℂ) x).re
  have hA : 0 < A := incG_genExpIntE_re_pos (p := p-1) (by linarith) hx
  have hB : 0 < B := incG_genExpIntE_re_pos (p := p) (by linarith) hx
  set α := B/A
  have hα : 0 < α := div_pos hB hA
  have i0 := incG_integrableOn_expInt (p := p-1) (by linarith) hx
  have i1 := incG_integrableOn_expInt (p := p) (by linarith) hx
  have i2 := incG_integrableOn_expInt (p := p+1) (by linarith) hx
  have eA : A = ∫ t in Ioi 1, Real.exp (-x*t)*t^(-(p-1)) := incG_genExpIntE_re_eq (p-1) hx
  have eB : B = ∫ t in Ioi 1, Real.exp (-x*t)*t^(-p) := incG_genExpIntE_re_eq p hx
  have eC : C = ∫ t in Ioi 1, Real.exp (-x*t)*t^(-(p+1)) := incG_genExpIntE_re_eq (p+1) hx
  have hI : α^2*A - 2*α*B + C = ∫ t in Ioi 1, (α^2*(Real.exp (-x*t)*t^(-(p-1))) -
      2*α*(Real.exp (-x*t)*t^(-p))) + Real.exp (-x*t)*t^(-(p+1)) := by
    rw [eA, eB, eC, ← integral_const_mul, ← integral_const_mul,
      ← integral_sub (i0.const_mul _) (i1.const_mul _)]
    exact (integral_add (((i0.const_mul _).sub (i1.const_mul _))) i2).symm
  have hk : ∀ t : ℝ, 0 < t → α^2*(Real.exp (-x*t)*t^(-(p-1))) - 2*α*(Real.exp (-x*t)*t^(-p)) +
      Real.exp (-x*t)*t^(-(p+1)) = Real.exp (-x*t)*t^(-(p+1))*(α*t-1)^2 := by
    intro t ht
    have e1 : t^(-(p-1)) = t^(-(p+1))*t^2 := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]; push_cast; ring_nf
    have e2 : t^(-p) = t^(-(p+1))*t := by
      rw [← Real.rpow_add_one ht.ne']; ring_nf
    rw [e1, e2]; ring
  have hpos : 0 < α^2*A - 2*α*B + C := by
    rw [hI]
    refine incG_setIntegral_Ioi_one_pos (((i0.const_mul _).sub (i1.const_mul _)).add i2)
      (c := 1/α) (fun t h1 => ?_) (fun t h1 h1' => ?_)
    · have ht : 0 < t := lt_trans one_pos (show (1:ℝ) < t from h1)
      rw [hk t ht]; positivity
    · have ht : 0 < t := lt_trans one_pos h1'
      rw [hk t ht]
      have : 1 < α*t := by rw [div_lt_iff₀ hα] at h1; linarith
      have : 0 < (α*t-1)^2 := by nlinarith
      positivity
  have : α^2*A - 2*α*B + C = C - B^2/A := by
    simp only [α]; field_simp; ring
  rw [this, sub_pos, div_lt_iff₀ hA] at hpos
  linarith

/-- DLMF 8.19.20 for natural order. -/
theorem incG_genExpIntE_logconvex {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (genExpIntE n x).re^2 < (genExpIntE (n-1 : ℕ) x).re*(genExpIntE (n+1) x).re := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h := incG_genExpIntE_logconvex_real hn1 hx
  have hc : (((n:ℝ)-1 : ℝ):ℂ) = ((n-1:ℕ):ℂ) := by rw [Nat.cast_sub hn]; push_cast; ring
  rw [hc] at h
  push_cast at h ⊢
  exact h

/-- Real derivative of `x ↦ Re E_p(x)`. -/
theorem incG_hasDerivAt_genExpIntE_re (p : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (genExpIntE p y).re) (-(genExpIntE (p-1) x).re) x := by
  have h := (hasDerivAt_genExpIntE p (z := (x:ℂ)) (Or.inl (by simpa using hx))).real_of_complex
  simpa using h

/-- DLMF 8.19.22 for natural order. -/
theorem incG_genExpIntE_ratio_derivative {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < deriv (fun y : ℝ => (genExpIntE n y).re/(genExpIntE (n-1 : ℕ) y).re) x := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc : (((n-1:ℕ):ℝ):ℂ) = (n:ℂ)-1 := by rw [Nat.cast_sub hn]; push_cast; ring
  have hA : 0 < (genExpIntE (n-1 : ℕ) x).re := by
    have := incG_genExpIntE_re_pos (p := ((n-1:ℕ):ℝ)) (by positivity) hx
    simpa using this
  have d1 := incG_hasDerivAt_genExpIntE_re (n:ℂ) hx
  have d2 := incG_hasDerivAt_genExpIntE_re ((n-1:ℕ):ℂ) hx
  have hd : HasDerivAt (fun y : ℝ => (genExpIntE n y).re/(genExpIntE (n-1 : ℕ) y).re) _ x :=
    d1.div d2 hA.ne'
  rw [hd.deriv]
  apply div_pos _ (by positivity)
  have hc' : ((n-1:ℕ):ℂ) = (n:ℂ)-1 := by rw [Nat.cast_sub hn]; simp
  rw [hc']
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1
    have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    have r0 := incG_genExpIntE_re_rec (-1) hx
    have hE0 : (genExpIntE 0 x).re = Real.exp (-x)/x := by
      rw [genExpIntE_zero hx0, ← ofReal_neg, ← ofReal_exp, ← ofReal_div, ofReal_re]
    have hb := (incG_genExpIntE_rational_bounds (n := 1) le_rfl hx).1
    norm_num at r0 hb ⊢
    rw [hE0] at r0 ⊢
    have hexp := Real.exp_pos (-x)
    have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hE : (genExpIntE (-1) x).re*x = Real.exp (-x) + Real.exp (-x)/x := by linarith
    rw [inv_lt_iff_one_lt_mul₀ (by linarith)] at hb
    have key : Real.exp (-x)*Real.exp (-x) < Real.exp (-x)*(x+1)*(genExpIntE 1 x).re := by
      have := mul_lt_mul_of_pos_left hb (mul_pos hexp hexp)
      nlinarith
    have hx2 : 0 < x^2 := by positivity
    rw [← mul_lt_mul_iff_of_pos_right hx2]
    have l : Real.exp (-x)/x*(Real.exp (-x)/x)*x^2 = Real.exp (-x)*Real.exp (-x) := by
      field_simp
    have r : (genExpIntE 1 x).re * (genExpIntE (-1) x).re * x^2 =
        Real.exp (-x)*(x+1)*(genExpIntE 1 x).re := by
      rw [show (genExpIntE 1 x).re * (genExpIntE (-1) x).re * x^2 =
        (genExpIntE 1 x).re * ((genExpIntE (-1) x).re * x) * x by ring, hE]
      field_simp
    rw [l, r]; exact key
  · have h2' : (2:ℝ) ≤ n := by exact_mod_cast h2
    have h := incG_genExpIntE_logconvex_real (p := (n:ℝ)-1) (by linarith) hx
    rw [show ((((n:ℝ)-1:ℝ)+1 : ℝ) : ℂ) = (n:ℂ) by push_cast; ring,
      show ((((n:ℝ)-1:ℝ)-1 : ℝ) : ℂ) = (n:ℂ)-1-1 by push_cast; ring,
      show (((n:ℝ)-1:ℝ) : ℂ) = (n:ℂ)-1 by push_cast; ring] at h
    nlinarith

/-- At positive real arguments, successive positive integral orders are strictly decreasing, with
the lower ratio bounded by `(n-1)/n`. -/
@[dlmf 8.19.E19]
theorem genExpIntE_nat_order_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ((n : ℝ)-1)/n*(genExpIntE n x).re < (genExpIntE (n+1) x).re ∧ (genExpIntE (n+1) x).re < (genExpIntE n x).re :=
  incG_genExpIntE_order_bounds hn hx

/-- Strict discrete log-convexity of the generalized exponential integral in its positive integral
order. -/
@[dlmf 8.19.E20]
theorem genExpIntE_nat_logconvex {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (genExpIntE n x).re^2 < (genExpIntE (n-1 : ℕ) x).re*(genExpIntE (n+1) x).re :=
  incG_genExpIntE_logconvex hn hx

/-- Bound the exponentially scaled generalized exponential integral between the reciprocal shifts
`1/(x+n)` and `1/(x+n-1)`. -/
@[dlmf 8.19.E21]
theorem genExpIntE_nat_rational_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    1/(x+n) < Real.exp x*(genExpIntE n x).re ∧ Real.exp x*(genExpIntE n x).re ≤ 1/(x+n-1) :=
  incG_genExpIntE_rational_bounds hn hx

/-- The ratio of successive positive integral orders has strictly positive derivative on the
positive real axis. -/
@[dlmf 8.19.E22]
theorem genExpIntE_nat_ratio_derivative {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < deriv (fun y : ℝ => (genExpIntE n y).re/(genExpIntE (n-1 : ℕ) y).re) x :=
  incG_genExpIntE_ratio_derivative hn hx

/-- Integrating the preceding-order generalized exponential integral along a horizontal ray gives
the current-order function. -/
@[dlmf 8.19.E23]
theorem genExpIntE_tail_integral (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => genExpIntE (p-1) (z+t)) 0 (genExpIntE p z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -genExpIntE p (z+t)) (genExpIntE (p-1) (z+t)) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -genExpIntE p w)
      (hasDerivAt_genExpIntE p (add_ofReal_mem_slitPlane hz ht)).neg).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun t : ℝ => genExpIntE (p-1) (z+t)) (Ici 0) := fun t ht =>
    (hasDerivAt_comp_add_ofReal (hasDerivAt_genExpIntE (p-1)
      (add_ofReal_mem_slitPlane hz ht))).continuousAt.continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -genExpIntE p (z+t)) atTop (𝓝 0) := by
    have h := ((tendsto_exp_neg_mul_kummerU_sectorAtTop 1 (2-p) (by norm_num : (0:ℝ) < 1/2)).comp
      (tendsto_add_ofReal_sectorAtTop z)).neg
    rw [neg_zero] at h
    refine h.congr' ?_
    have := (tendsto_norm_sectorAtTop (1/2)).comp (tendsto_add_ofReal_sectorAtTop z)
    filter_upwards [this.eventually_gt_atTop 0] with t ht
    have ht0 : z+t ≠ 0 := by intro h0; simp [h0] at ht
    simp [genExpIntE_eq_exp_mul_kummerU p ht0]
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  simpa using h

/-- The displayed formula also needs Re b>0 for convergence at zero. -/
@[dlmf 8.19.E25]
theorem genExpIntE_mellin_laplace {a b p : ℂ} (ha : -1 < a.re) (hb : 0 < b.re) (hpb : 1 < (p+b).re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*(t : ℂ)^(b-1)*genExpIntE p t)=Gamma b*(1+a)^(-b)/(p+b-1)*Gamma (p+b)*DLMF.Hypergeometric.regularizedGaussHG 1 b (p+b) (a/(1+a)) := by
  have hz : 0 < (1+a).re := by simp; linarith
  have hz0 : (1+a) ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have hL := laplace_kummerU (a := p) (b := b+p-1) (c := p) (z := 1+a)
    (by simp at hpb ⊢; linarith) (by simp; linarith) hz
  have hI : (∫ t : ℝ in Ioi 0, exp (-a*t)*(t : ℂ)^(b-1)*genExpIntE p t) =
      ∫ t : ℝ in Ioi 0, exp (-(1+a)*t)*(t : ℂ)^(b+p-1-1)*kummerU p p t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [genExpIntE_eq_cpow_mul_kummerU, show b+p-1-1 = (b-1)+(p-1) by ring, cpow_add _ _ ht0,
      show -(1+a)*(t:ℂ) = -a*t + -t by ring, Complex.exp_add]
    ring
  rw [hI, hL]
  have hx : 1 - (1+a)⁻¹ = a/(1+a) := by field_simp; ring
  have hcut : a/(1+a) ∈ cutPlane := by
    rw [mem_cutPlane, ← hx, sub_sub_cancel]
    exact Or.inl (by rw [inv_re]; exact div_pos hz (normSq_pos.mpr hz0))
  rw [hx, show p+(b+p-1)-p+1 = p+b by ring, show b+p-1-p+1 = b by ring,
    regularizedGaussHG_euler _ _ _ hcut,
    show p+b-p = b by ring, show p+b-(b+p-1) = 1 by ring, show b-(b+p-1) = 1-p by ring,
    regularizedGaussHG_symm b 1 _ hcut, ← hx, sub_sub_cancel,
    inv_cpow _ _ (by
      intro h
      have := (arg_eq_pi_iff.mp h).1
      linarith)]
  have hpb1 : p+b-1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this hpb; linarith
  have hG : Gamma (p+b) = (p+b-1)*Gamma (p+b-1) := by
    rw [← Complex.Gamma_add_one _ hpb1]; ring_nf
  have hc : (1+a)^(-(b+p-1)) = (1+a)^(-b) * (1+a)^(1-p) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  have hc1 : (1+a)^(1-p) ≠ 0 := by simp [hz0]
  rw [hG, hc, show b+p-1 = p+b-1 by ring]
  field_simp

/-- Estimate under the stated parameter and domain assumptions: `0 < (1 + a*u).re`. -/
theorem incG_one_add_mul_re_pos {a : ℂ} (ha : -1 < a.re) {u : ℝ} (hu : u ∈ Set.uIcc (0:ℝ) 1) :
    0 < (1 + a*u).re := by
  rw [Set.uIcc_of_le zero_le_one] at hu
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  rcases le_or_gt 0 a.re with h | h
  · nlinarith [hu.1]
  · nlinarith [hu.1, hu.2]

/-- The function `(fun u : ℝ => (u:ℂ)^m/(1+a*u))` is continuous on `(Set.uIcc 0 1)`. -/
theorem incG_continuousOn_powDiv {a : ℂ} (ha : -1 < a.re) (m : ℕ) :
    ContinuousOn (fun u : ℝ => (u:ℂ)^m/(1+a*u)) (Set.uIcc 0 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu h0 => ?_
  have := incG_one_add_mul_re_pos ha hu; rw [h0] at this; simp at this

/-- The finite integral `J_n(a) = ∫₀¹ u^{n-1}/(1+au) du` in closed form. -/
theorem incG_laplaceJ_recurrence {a : ℂ} (ha : -1 < a.re) (m : ℕ) :
    a * (∫ u in (0:ℝ)..1, (u:ℂ)^(m+1)/(1+a*u)) =
      1/(m+1) - ∫ u in (0:ℝ)..1, (u:ℂ)^m/(1+a*u) := by
  have hi : IntervalIntegrable (fun u : ℝ => (u:ℂ)^m/(1+a*u)) volume 0 1 :=
    (incG_continuousOn_powDiv ha m).intervalIntegrable
  have hp : (∫ u in (0:ℝ)..1, (u:ℂ)^m) = 1/(m+1) := by
    have : (∫ u in (0:ℝ)..1, (u:ℂ)^m) = ((∫ u in (0:ℝ)..1, u^m : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]; simp
    rw [this, integral_pow]; push_cast; simp
  rw [← hp, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((by fun_prop : Continuous fun u : ℝ => (u:ℂ)^m).intervalIntegrable 0 1) hi]
  refine intervalIntegral.integral_congr fun u hu => ?_
  have h0 : 1 + a*u ≠ 0 := by
    intro h0; have := incG_one_add_mul_re_pos ha hu; rw [h0] at this; simp at this
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ u in (0:ℝ)..1,
(u:ℂ)^0/(1+a*u)) = log (1+a)/a`. -/
theorem incG_laplaceJ_one {a : ℂ} (ha : -1 < a.re) (ha0 : a ≠ 0) :
    (∫ u in (0:ℝ)..1, (u:ℂ)^0/(1+a*u)) = log (1+a)/a := by
  have hd : ∀ u ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun u : ℝ => log (1+a*u)/a) ((u:ℂ)^0/(1+a*u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => 1+a*(u:ℂ)) a u := by
      simpa using ((hasDerivAt_id u).ofReal_comp.const_mul a).const_add 1
    have h2 := (h1.clog_real (Or.inl (incG_one_add_mul_re_pos ha hu))).div_const a
    convert h2 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((incG_continuousOn_powDiv ha 0).intervalIntegrable)]
  simp

/-- Formula under the stated hypotheses: `(∫ u in (0:ℝ)..1, (u:ℂ)^m/(1+a*u)) = (-1 :
ℂ)^m/a^(m+1)*(log (1+a)+∑ k ∈ Finset.range m, (-1 : ℂ)^(k+1)*a^(k+1)/(k+1))`. -/
theorem incG_laplaceJ_closed {a : ℂ} (ha : -1 < a.re) (ha0 : a ≠ 0) (m : ℕ) :
    (∫ u in (0:ℝ)..1, (u:ℂ)^m/(1+a*u)) = (-1 : ℂ)^m/a^(m+1)*(log (1+a)+∑ k ∈ Finset.range m, (-1 : ℂ)^(k+1)*a^(k+1)/(k+1)) := by
  induction m with
  | zero => rw [incG_laplaceJ_one ha ha0]; simp; ring
  | succ m ih =>
    have hr := incG_laplaceJ_recurrence ha m
    rw [ih] at hr
    have hpow : ((-1:ℂ)^(m+1))*((-1)^(m+1)) = 1 := by rw [← mul_pow]; simp
    have hm : (m:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [Finset.sum_range_succ]
    apply mul_left_cancel₀ ha0
    rw [hr]
    field_simp
    have hpow2 : (-1:ℂ)^(m*2) = 1 := by rw [mul_comm, pow_mul]; simp
    linear_combination (-(a^3*a^(m*2))) * hpow2

/-- Identity under the stated parameter and domain assumptions: `(∫ u in (0:ℝ)..1,
(u:ℂ)^m/(1+0*u)) = 1/(m+1)`. -/
theorem incG_laplaceJ_zero (m : ℕ) :
    (∫ u in (0:ℝ)..1, (u:ℂ)^m/(1+0*u)) = 1/(m+1) := by
  have : (∫ u in (0:ℝ)..1, (u:ℂ)^m) = ((∫ u in (0:ℝ)..1, u^m : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; simp
  simp only [zero_mul, add_zero, div_one]
  rw [this, integral_pow]; push_cast; simp

/-- The Laplace transform of `E_n` as a finite integral, via 8.19.25. -/
theorem incG_genExpIntE_laplace_eq {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE n t) =
      ∫ u in (0:ℝ)..1, (u:ℂ)^(n-1)/(1+a*u) := by
  have hz : 0 < (1+a).re := by simp; linarith
  have hz0 : (1+a) ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have h := genExpIntE_mellin_laplace (a := a) (b := 1) (p := n) ha (by simp)
    (by simp; omega)
  have hI : (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE n t) =
      ∫ t : ℝ in Ioi 0, exp (-a*t)*(t : ℂ)^((1:ℂ)-1)*genExpIntE n t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp
  have hx : 1 - (1+a)⁻¹ = a/(1+a) := by field_simp; ring
  have hcut : a/(1+a) ∈ cutPlane := by
    rw [mem_cutPlane, ← hx, sub_sub_cancel]
    exact Or.inl (by rw [inv_re]; exact div_pos hz (normSq_pos.mpr hz0))
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [hI, h, regularizedGaussHG_eq_regularizedGaussHGIntegral (by simp) (by simp; omega) hcut,
    regularizedGaussHGIntegral]
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hK : ∀ t ∈ Set.uIcc (0:ℝ) 1, eulerKernel 1 1 ((((m+1:ℕ)):ℂ)+1) (a/(1+a)) t =
      (1+a) * (((1-t:ℝ):ℂ)^m/(1+a*((1-t:ℝ):ℂ))) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hden : 1+a*((1-t:ℝ):ℂ) ≠ 0 := by
      intro h0
      have := incG_one_add_mul_re_pos ha (u := 1-t)
        (by rw [Set.uIcc_of_le zero_le_one]; constructor <;> linarith [ht.1, ht.2])
      rw [h0] at this; simp at this
    rw [eulerKernel, sub_self, cpow_zero, one_mul, cpow_neg_one,
      show (((m+1:ℕ)):ℂ)+1-1-1 = ((m:ℕ):ℂ) by push_cast; ring, cpow_natCast]
    have h1 : 1 - a/(1+a)*(t:ℂ) = (1+a*((1-t:ℝ):ℂ))/(1+a) := by
      push_cast; field_simp; ring
    rw [h1]; push_cast; field_simp
  rw [intervalIntegral.integral_congr hK, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun u : ℝ => (u:ℂ)^m/(1+a*u)) 1]
  simp only [sub_zero, sub_self]
  have hf : ((m+1:ℕ).factorial : ℂ) = (m+1:ℕ) * (m.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hG : Gamma ((m+1:ℕ):ℂ) = m.factorial := by
    rw [Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  rw [Gamma_one, cpow_neg_one, add_sub_cancel_right, hG, Complex.Gamma_nat_eq_factorial, hf]
  field_simp

/-- Laplace transform of the generalized exponential integral at positive integral order,
including the removable value at zero. -/
theorem incG_genExpIntE_nat_laplace {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE n t)=if a=0 then 1/(n : ℂ) else (-1 : ℂ)^(n-1)/a^n*(log (1+a)+∑ k ∈ Finset.range (n-1), (-1 : ℂ)^(k+1)*a^(k+1)/(k+1)) := by
  rw [incG_genExpIntE_laplace_eq hn ha]
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  split_ifs with ha0
  · subst ha0; rw [incG_laplaceJ_zero]; push_cast; rfl
  · exact incG_laplaceJ_closed ha ha0 m

/-- Laplace transform of the generalized exponential integral at positive integral order,
including the removable value at zero. -/
@[dlmf 8.19.E24]
theorem genExpIntE_nat_laplace {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE n t)=if a=0 then 1/(n : ℂ) else (-1 : ℂ)^(n-1)/a^n*(log (1+a)+∑ k ∈ Finset.range (n-1), (-1 : ℂ)^(k+1)*a^(k+1)/(k+1)) :=
  incG_genExpIntE_nat_laplace hn ha

/-- The auxiliary integral L(p) for positive p. -/
@[dlmf 8.19.E27]
def genExpIntL (p : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, exp (-t : ℂ)*genExpIntE p t

/-- Express the exponentially weighted integral of the generalized exponential integral as a
regularized Gauss hypergeometric value at one half. -/
@[dlmf 8.19.E27]
theorem genExpIntL_hypergeometric {p : ℝ} (hp : 0 < p) :
    genExpIntL p=Gamma (1+(p : ℂ))/(2*p)*DLMF.Hypergeometric.regularizedGaussHG 1 1 (1+p) (1/2) := by
  have h := genExpIntE_mellin_laplace (a := 1) (b := 1) (p := p) (by norm_num) (by norm_num)
    (by simp; linarith)
  rw [genExpIntL]
  have hI : (∫ t : ℝ in Ioi 0, exp (-t : ℂ)*genExpIntE p t) =
      ∫ t : ℝ in Ioi 0, exp (-1*t)*(t : ℂ)^((1:ℂ)-1)*genExpIntE p t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp
  rw [hI, h, Gamma_one, show (1:ℂ)+1 = 2 by norm_num, add_comm (p:ℂ) 1, cpow_neg_one]
  have hp0 : (p:ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  rw [show (1:ℂ)+p-1 = p by ring]
  field_simp

/-- The shift `u = 1 + v` on `(1, ∞)`. -/
theorem incGP_integral_Ioi_one_shift (g : ℝ → ℝ) :
    ∫ s in Ioi (1 : ℝ), g s = ∫ t in Ioi (0 : ℝ), g (1 + t) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h : ∀ t : ℝ, (Ioi (0 : ℝ)).indicator (fun t => g (1 + t)) t =
      (Ioi (1 : ℝ)).indicator g (1 + t) := by
    intro t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht),
        indicator_of_mem (show 1 + t ∈ Ioi 1 by simp [ht])]
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht),
        indicator_of_notMem (show 1 + t ∉ Ioi 1 by simpa using ht)]
  simp_rw [h]
  exact (integral_add_left_eq_self (fun u => (Ioi (1 : ℝ)).indicator g u) 1).symm

/-- `E_p(x) ≤ Γ(1-s) x^{s-1} e^{-x}` for real `0 ≤ s < 1`, `s ≤ p`, `x > 0`. -/
theorem incGP_genExpIntE_re_le {p s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hsp : s ≤ p) {x : ℝ}
    (hx : 0 < x) :
    (genExpIntE p x).re ≤ Real.Gamma (1 - s) * x ^ (s - 1) * Real.exp (-x) := by
  rw [incG_genExpIntE_re_eq p hx, incGP_integral_Ioi_one_shift]
  have hI : ∫ v in Ioi (0 : ℝ), v ^ (-s) * Real.exp (-x * v ^ (1 : ℝ)) =
      x ^ (-(-s + 1) / 1) * (1 / 1) * Real.Gamma ((-s + 1) / 1) :=
    _root_.integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith) hx
  have hInt : IntegrableOn (fun v : ℝ => v ^ (-s) * Real.exp (-x * v ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hx
  have key : ∫ v in Ioi (0 : ℝ), Real.exp (-x * (1 + v)) * (1 + v) ^ (-p) ≤
      ∫ v in Ioi (0 : ℝ), Real.exp (-x) * (v ^ (-s) * Real.exp (-x * v ^ (1 : ℝ))) := by
    refine integral_mono_of_nonneg ?_ (hInt.const_mul _) ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
      have : (0 : ℝ) < v := hv
      positivity
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
      have hv0 : (0 : ℝ) < v := hv
      dsimp only
      rw [Real.rpow_one, show -x * (1 + v) = -x + -x * v by ring, Real.exp_add]
      have h1 : (1 + v) ^ (-p) ≤ (1 + v) ^ (-s) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have h2 : (1 + v) ^ (-s) ≤ v ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hv0 (by linarith) (by linarith)
      have h3 : 0 < Real.exp (-x) * Real.exp (-x * v) := by positivity
      calc Real.exp (-x) * Real.exp (-x * v) * (1 + v) ^ (-p)
          ≤ Real.exp (-x) * Real.exp (-x * v) * v ^ (-s) := by
            gcongr; exact h1.trans h2
        _ = _ := by ring
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, hI]
  simp only [div_one, mul_one]
  rw [show -(-s + 1) = s - 1 by ring, show -s + 1 = 1 - s by ring]
  ring

/-- For real `p` and `x > 0`, `E_p(x)` is real. -/
theorem incGP_genExpIntE_ofReal (p : ℝ) {x : ℝ} (hx : 0 < x) :
    genExpIntE p x = ((genExpIntE p x).re : ℂ) := by
  rw [incG_genExpIntE_re_eq p hx, genExpIntE_eq_integral (p:ℂ) hx]
  rw [show ((∫ t in Ioi 1, Real.exp (-x*t)*t^(-p) : ℝ) : ℂ) =
    ∫ t in Ioi (1:ℝ), ((Real.exp (-x*t)*t^(-p) : ℝ) : ℂ) from integral_ofReal.symm]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
  rw [Complex.real_smul, ofReal_mul, ofReal_cpow ht0]; push_cast; ring_nf

/-- Integrability of `t^σ e^{-2t}` on `(0,∞)` for `σ > -1`. -/
theorem incGP_integrableOn {σ : ℝ} (hσ : -1 < σ) (C : ℝ) :
    IntegrableOn (fun t : ℝ => C * (t ^ σ * Real.exp (-2 * t ^ (1 : ℝ)))) (Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_rpow hσ one_pos two_pos).const_mul C

/-- Choose smaller integrable exponents below `p` and `q` whose sum still exceeds one.
This isolates the endpoint integrability conditions in the product Laplace integral. -/
private lemma exists_auxiliary_exponents_for_product_integral {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p + q) :
    ∃ s s' : ℝ, 0 < s ∧ s < 1 ∧ s ≤ p ∧ 0 < s' ∧ s' < 1 ∧ s' ≤ q ∧ 1 < s + s' := by
  set m := max (max (1 / 2 : ℝ) (1 - p)) (1 - q) with hm
  have hm1 : m < 1 := max_lt (max_lt (by norm_num) (by linarith)) (by linarith)
  have hm2 : 1 / 2 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hm3 : 1 - p ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hm4 : 1 - q ≤ m := le_max_right _ _
  set θ := (1 + m) / 2 with hθ
  set s := min p θ
  set s' := min q θ
  have hs0 : 0 < s := lt_min hp (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsp : s ≤ p := min_le_left _ _
  have hs0' : 0 < s' := lt_min hq (by linarith)
  have hs1' : s' < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsq : s' ≤ q := min_le_left _ _
  have hss : 1 < s + s' := by
    simp only [s, s', min_def]
    split_ifs <;> linarith
  exact ⟨s, s', hs0, hs1, hsp, hs0', hs1', hsq, hss⟩

/-- The integral of the product `E_p E_q` is the sum of their exponentially weighted integrals
divided by `p+q-1`; positivity and `p+q>1` ensure integrability. -/
@[dlmf 8.19.E26]
theorem genExpIntE_product_integral {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p+q) :
    (∫ t : ℝ in Ioi 0, genExpIntE p t*genExpIntE q t)=(genExpIntL p+genExpIntL q)/(p+q-1) := by
  obtain ⟨s, s', hs0, hs1, hsp, hs0', hs1', hsq, hss⟩ :=
    exists_auxiliary_exponents_for_product_integral hp hq hpq

  set e : ℝ → ℝ → ℝ := fun r t => (genExpIntE (r : ℂ) (t : ℂ)).re with he
  set Cp := Real.Gamma (1 - s)
  set Cq := Real.Gamma (1 - s')
  have hCp : 0 < Cp := Real.Gamma_pos_of_pos (by linarith)
  have hCq : 0 < Cq := Real.Gamma_pos_of_pos (by linarith)
  have hbp : ∀ t : ℝ, 0 < t → e p t ≤ Cp * t ^ (s - 1) * Real.exp (-t) :=
    fun t ht => incGP_genExpIntE_re_le hs0.le hs1 hsp ht
  have hbq : ∀ t : ℝ, 0 < t → e q t ≤ Cq * t ^ (s' - 1) * Real.exp (-t) :=
    fun t ht => incGP_genExpIntE_re_le hs0'.le hs1' hsq ht
  have hpp : ∀ t : ℝ, 0 < t → 0 < e p t := fun t ht => incG_genExpIntE_re_pos hp.le ht
  have hpq : ∀ t : ℝ, 0 < t → 0 < e q t := fun t ht => incG_genExpIntE_re_pos hq.le ht
  have hderE : ∀ r : ℝ, ∀ t : ℝ, 0 < t → HasDerivAt (e r) (-e (r - 1) t) t := by
    intro r t ht
    have := incG_hasDerivAt_genExpIntE_re (r : ℂ) ht
    simpa [e] using this
  have hcontE : ∀ r : ℝ, ContinuousOn (e r) (Ioi 0) := fun r t ht =>
    (hderE r t ht).continuousAt.continuousWithinAt
  have hrec : ∀ r : ℝ, ∀ t : ℝ, 0 < t → t * e (r - 1) t = Real.exp (-t) - (r - 1) * e r t := by
    intro r t ht
    have := incG_genExpIntE_re_rec (r - 1) ht
    simp only [e]
    push_cast at this ⊢
    rw [show (r : ℂ) - 1 + 1 = r by ring] at this
    linarith
  -- pointwise bounds
  have hb1 : ∀ t : ℝ, 0 < t → ‖e p t * e q t‖ ≤
      Cp * Cq * (t ^ (s + s' - 2) * Real.exp (-2 * t ^ (1 : ℝ))) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hpp t ht) (hpq t ht)), Real.rpow_one,
      show s + s' - 2 = (s - 1) + (s' - 1) by ring, Real.rpow_add ht,
      show -2 * t = -t + -t by ring, Real.exp_add]
    calc e p t * e q t ≤ (Cp * t ^ (s - 1) * Real.exp (-t)) * (Cq * t ^ (s' - 1) * Real.exp (-t)) :=
          mul_le_mul (hbp t ht) (hbq t ht) (hpq t ht).le (by positivity)
      _ = _ := by ring
  have hb2 : ∀ r σ C : ℝ, 0 < C → (∀ t : ℝ, 0 < t → 0 < e r t) →
      (∀ t : ℝ, 0 < t → e r t ≤ C * t ^ σ * Real.exp (-t)) →
      ∀ t : ℝ, 0 < t → ‖Real.exp (-t) * e r t‖ ≤ C * (t ^ σ * Real.exp (-2 * t ^ (1 : ℝ))) := by
    intro r σ C hC hpos hb t ht
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (hpos t ht)), Real.rpow_one,
      show -2 * t = -t + -t by ring, Real.exp_add]
    calc Real.exp (-t) * e r t ≤ Real.exp (-t) * (C * t ^ σ * Real.exp (-t)) := by
          gcongr; exact hb t ht
      _ = _ := by ring
  -- integrability
  have hmeas : ∀ g : ℝ → ℝ, ContinuousOn g (Ioi 0) → AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    fun g hg => hg.aestronglyMeasurable measurableSet_Ioi
  have hI1 : IntegrableOn (fun t => e p t * e q t) (Ioi 0) := by
    refine (incGP_integrableOn (σ := s + s' - 2) (by linarith) (Cp * Cq)).mono' (hmeas _ ((hcontE p).mul (hcontE q))) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hb1 t ht)
  have hI2 : ∀ r σ C : ℝ, 0 < C → -1 < σ → (∀ t : ℝ, 0 < t → 0 < e r t) →
      (∀ t : ℝ, 0 < t → e r t ≤ C * t ^ σ * Real.exp (-t)) →
      IntegrableOn (fun t => Real.exp (-t) * e r t) (Ioi 0) := by
    intro r σ C hC hσ hpos hb
    refine (incGP_integrableOn hσ C).mono'
      (hmeas _ ((Real.continuous_exp.comp continuous_neg).continuousOn.mul (hcontE r))) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => hb2 r σ C hC hpos hb t ht)
  have hIp := hI2 p (s - 1) Cp hCp (by linarith) hpp hbp
  have hIq := hI2 q (s' - 1) Cq hCq (by linarith) hpq hbq
  -- fundamental theorem of calculus for `t E_p E_q`
  set f : ℝ → ℝ := fun t => t * e p t * e q t
  set f' : ℝ → ℝ := fun t => (p + q - 1) * (e p t * e q t) -
    (Real.exp (-t) * e p t + Real.exp (-t) * e q t)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have h1 := hrec p t ht0
    have h2 := hrec q t ht0
    refine (((hasDerivAt_id' t).mul (hderE p t ht0)).mul (hderE q t ht0)).congr_deriv ?_
    simp only [f']
    have key : ((fun x : ℝ => x) * e p) t = t * e p t := rfl
    rw [key]
    linear_combination (-(e q t)) * h1 - (e p t) * h2
  have hfbound : ∀ t : ℝ, 0 < t → ‖f t‖ ≤ Cp * Cq * (t ^ (s + s' - 1) * Real.exp (-2 * t)) := by
    intro t ht
    have := hb1 t ht
    rw [Real.rpow_one] at this
    simp only [f, norm_mul, mul_assoc, Real.norm_eq_abs, abs_of_pos ht] at this ⊢
    rw [show s + s' - 1 = 1 + (s + s' - 2) by ring, Real.rpow_add ht, Real.rpow_one]
    rw [← abs_mul] at this ⊢
    calc t * |e p t * e q t| ≤ t * (Cp * (Cq * (t ^ (s + s' - 2) * Real.exp (-2 * t)))) := by
          gcongr
      _ = _ := by ring
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have hf0 : f 0 = 0 := by simp [f]
    rw [ContinuousWithinAt, hf0]
    have hr : 0 < s + s' - 1 := by linarith
    have hg : Tendsto (fun t : ℝ => Cp * Cq * t ^ (s + s' - 1)) (𝓝[Ici 0] 0) (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 (s + s' - 1) (Or.inr hr.le)).const_mul (Cp * Cq))
      have h0 : Cp * Cq * (0 : ℝ) ^ (s + s' - 1) = 0 := by rw [Real.zero_rpow hr.ne', mul_zero]
      have := this.tendsto
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with t ht
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with h0 | h0
    · subst h0; simp [f, Real.zero_rpow hr.ne']
    · refine (hfbound t h0).trans ?_
      have : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have : 0 ≤ t ^ (s + s' - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right this (by assumption))
        (mul_pos hCp hCq).le
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hg := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s + s' - 1) 2 two_pos).const_mul
      (Cp * Cq)
    rw [mul_zero] at hg
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact hfbound t ht
  have hf'int : IntegrableOn f' (Ioi 0) :=
    (hI1.const_mul (p + q - 1)).sub (hIp.add hIq)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf'int hlim
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, sub_zero] at hFTC
  have hreal : (p + q - 1) * (∫ t in Ioi 0, e p t * e q t) =
      (∫ t in Ioi 0, Real.exp (-t) * e p t) + ∫ t in Ioi 0, Real.exp (-t) * e q t := by
    simp only [f'] at hFTC
    have hs := integral_sub (hI1.const_mul (p + q - 1)) (hIp.add hIq)
    simp only [Pi.add_apply] at hs
    rw [hs, integral_const_mul, integral_add hIp hIq] at hFTC
    linarith
  -- back to complex values
  have hc1 : (∫ t : ℝ in Ioi 0, genExpIntE p t * genExpIntE q t) =
      ((∫ t in Ioi 0, e p t * e q t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [incGP_genExpIntE_ofReal p ht, incGP_genExpIntE_ofReal q ht]
    push_cast; rfl
  have hc2 : ∀ r : ℝ, genExpIntL r = ((∫ t in Ioi 0, Real.exp (-t) * e r t : ℝ) : ℂ) := by
    intro r
    rw [genExpIntL, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [incGP_genExpIntE_ofReal r ht]
    push_cast; rfl
  have hne : (p : ℂ) + q - 1 ≠ 0 := by
    rw [show (p : ℂ) + q - 1 = ((p + q - 1 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (by linarith)
  rw [hc1, hc2, hc2, eq_div_iff hne]
  rw [show (p : ℂ) + q - 1 = ((p + q - 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_mul, ← ofReal_add,
    mul_comm, hreal]

/-- The error-to-exponential-integral relation with its square-argument continuation. -/
@[dlmf 7.11.E3]
theorem erfc_genExpIntEOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=z/Real.sqrt π*genExpIntEOnLog (1/2) (2*log z) := by
  rw [genExpIntEOnLog, show (1:ℂ)-1/2 = 1/2 by norm_num, upperIncGammaOnLog_half,
    show 2*log z/2=log z by ring, Complex.exp_log hz,
    show ((1:ℂ)/2-1)*(2*log z) = -log z by ring, Complex.exp_neg, Complex.exp_log hz]
  have hp : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

end DLMF.Confluent
