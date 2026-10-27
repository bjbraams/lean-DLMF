/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Defs
public import DLMF.Mathieu.Noninteger.Fourier
public import DLMF.Bessel.SecondKind

/-!
# Convergence of the cross-product series of the modified Mathieu functions (DLMF 28.24.1)

Infrastructure for DLMF 28.24.1:

* the order recurrences of the continued Bessel functions `besselJExp`, `besselYExp`
  (`p2m_besselJExp_rec`, `p2m_besselYExp_rec`; integer orders of `Y` by continuity in the order)
  and of the cylinder functions `mathieuCylExp j`;
* growth `‖u_k‖ ≤ E A^{|k|} |k|!` of any solution of the Bessel order recurrence
  (`p2m_growth_int`) and decay `‖c_m‖ (|m|!)² ≤ C K^{|m|}` of any bounded solution of the
  Mathieu coefficient recurrence 28.14.4 (`p2m_decay_int`);
* the abstract cross-product theorem `p2m_cross_series`: the series
  `S_n = ∑_ℓ (-1)^ℓ c_ℓ J_{ℓ-n}(x) 𝒞_{n+ℓ}(y)` (`xy = q`) converge absolutely, satisfy the
  recurrence 28.14.4 in `n` (termwise from the Bessel recurrences), and since their growth is at
  most `R^{|n|} |n|!` their Casoratian with `c` vanishes, so `S_n = L c_n`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Nat

namespace DLMF.Mathieu

/-- For integer order, `besselJExp k h w = J_k(h e^w)` for all `h`, `w`. -/
theorem p1c_besselJExp_intCast (k : ℤ) (h w : ℂ) :
    besselJExp k h w = besselJ k (h * Complex.exp w) := by
  rw [besselJExp, DLMF.Bessel.besselJ_eq_regularized, cpow_intCast, cpow_intCast,
    Complex.exp_int_mul, show h * Complex.exp w / 2 = h / 2 * Complex.exp w by ring, mul_zpow]

/-- `J_{-k} = (-1)^k J_k` for the continued Bessel function of integer order. -/
theorem p1c_besselJExp_neg_intCast (k : ℤ) (h w : ℂ) :
    besselJExp ((-k : ℤ) : ℂ) h w = (-1 : ℂ) ^ k * besselJExp k h w := by
  rw [p1c_besselJExp_intCast, p1c_besselJExp_intCast, Int.cast_neg, besselJ_neg_int]

/-- `Y_μ(h e^z)` (continued) for noninteger `μ`. -/
theorem p1c_besselYExp_of_not_int {μ : ℂ} (hμ : ¬ ∃ k : ℤ, μ = k) (h z : ℂ) :
    besselYExp μ h z = (besselJExp μ h z * Complex.cos (μ * π) - besselJExp (-μ) h z) /
      Complex.sin (μ * π) := by
  simp only [besselYExp, hμ, ↓reduceIte]

/-- The order recurrence of the continued `J`: `J_{μ-1} + J_{μ+1} = (2μ/(h e^z)) J_μ`. -/
theorem p2m_besselJExp_rec (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselJExp (μ - 1) h z + besselJExp (μ + 1) h z =
      2 * μ / (h * Complex.exp z) * besselJExp μ h z := by
  have he := DLMF.Bessel.regularized0F1_contiguous μ (-((h * Complex.exp z) ^ 2 / 4))
  have h2 : h / 2 ≠ 0 := div_ne_zero hh two_ne_zero
  simp only [besselJExp]
  rw [cpow_sub _ _ h2, cpow_add _ _ h2, cpow_one, show μ - 1 + 1 = μ by ring]
  have hx : Complex.exp ((μ - 1) * z) = Complex.exp (μ * z) / Complex.exp z := by
    rw [← Complex.exp_sub]; ring_nf
  have hy : Complex.exp ((μ + 1) * z) = Complex.exp (μ * z) * Complex.exp z := by
    rw [← Complex.exp_add]; ring_nf
  rw [hx, hy]
  have hez := Complex.exp_ne_zero z
  have hp : (h / 2) ^ μ ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h' => h2 h'.1
  linear_combination (norm := (field_simp; ring))
    (2 * (h / 2) ^ μ * Complex.exp (μ * z) / (h * Complex.exp z)) * he


/-- The continued `J_μ(h e^z)` is entire in the order `μ` for `h ≠ 0`. -/
theorem p2m_differentiable_besselJExp_order {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    Differentiable ℂ fun μ : ℂ => besselJExp μ h z := by
  have h2 : h / 2 ≠ 0 := div_ne_zero hh two_ne_zero
  simp only [besselJExp]
  exact ((differentiable_id.const_cpow (Or.inl h2)).mul (by fun_prop)).mul
    ((DLMF.Bessel.differentiable_regularized0F1_param _).comp (differentiable_id.add_const 1))

/-- The numerator `J_μ cos μπ - J_{-μ}` of the continued `Y_μ`. -/
def p2m_besselDExp (μ h z : ℂ) : ℂ :=
  besselJExp μ h z * Complex.cos (μ * π) - besselJExp (-μ) h z

theorem p2m_differentiable_besselDExp {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    Differentiable ℂ fun μ : ℂ => p2m_besselDExp μ h z := by
  unfold p2m_besselDExp
  exact ((p2m_differentiable_besselJExp_order hh z).mul (by fun_prop)).sub
    ((p2m_differentiable_besselJExp_order hh z).comp differentiable_neg)

lemma p2m_besselDExp_int (n : ℤ) (h z : ℂ) : p2m_besselDExp n h z = 0 := by
  have := p1c_besselJExp_neg_intCast n h z
  rw [p2m_besselDExp, DLMF.Bessel.cos_int_mul_pi_complex, ← Int.cast_neg, this]; ring

theorem p2m_besselYExp_of_not_int {μ : ℂ} (hμ : ∀ k : ℤ, μ ≠ k) (h z : ℂ) :
    besselYExp μ h z = p2m_besselDExp μ h z / Complex.sin (μ * π) :=
  p1c_besselYExp_of_not_int (fun ⟨k, hk⟩ => hμ k hk) h z

/-- Near an integer `n`, the continued `Y_μ` is a quotient of difference quotients. -/
theorem p2m_besselYExp_eq_dslope (n : ℤ) {μ h : ℂ} (hμ : μ ∈ Metric.ball (n : ℂ) (1 / 2))
    (hh : h ≠ 0) (z : ℂ) :
    besselYExp μ h z = dslope (fun ν => p2m_besselDExp ν h z) n μ /
      dslope (fun ν : ℂ => Complex.sin (ν * π)) n μ := by
  by_cases hne : μ = n
  · subst hne
    have hD := p2m_differentiable_besselDExp hh z
    have hcont : ContinuousAt (fun μ => dslope (fun ν => p2m_besselDExp ν h z) n μ /
        dslope (fun ν : ℂ => Complex.sin (ν * π)) n μ) n :=
      (continuousAt_dslope_same.mpr (hD n)).div
        (continuousAt_dslope_same.mpr (by fun_prop)) (DLMF.Bessel.dslope_sin_ne_zero n
          (Metric.mem_ball_self (by norm_num)))
    have ht : Tendsto (fun μ => (besselJExp μ h z * Complex.cos (μ * π) - besselJExp (-μ) h z) /
        Complex.sin (μ * π)) (𝓝[≠] (n : ℂ))
        (𝓝 (dslope (fun ν => p2m_besselDExp ν h z) n n /
          dslope (fun ν : ℂ => Complex.sin (ν * π)) n n)) := by
      refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with μ hμ
      rw [dslope_of_ne _ hμ, dslope_of_ne _ hμ, slope_def_field, slope_def_field,
        p2m_besselDExp_int, DLMF.Bessel.sin_int_mul_pi_complex, sub_zero, sub_zero]
      have hμn : μ - n ≠ 0 := sub_ne_zero.mpr hμ
      simp only [p2m_besselDExp]
      field_simp
    have hex : ∃ k : ℤ, (n : ℂ) = k := ⟨n, rfl⟩
    simp only [besselYExp, hex, ite_true]
    exact ht.limUnder_eq
  · rw [p2m_besselYExp_of_not_int (DLMF.Bessel.not_int_of_mem_ball hμ hne), dslope_of_ne _ hne,
      dslope_of_ne _ hne, slope_def_field, slope_def_field, p2m_besselDExp_int,
      DLMF.Bessel.sin_int_mul_pi_complex, sub_zero, sub_zero]
    have hμn : μ - n ≠ 0 := sub_ne_zero.mpr hne
    field_simp

/-- The continued `Y_μ(h e^z)` is continuous in the order `μ`, including integer orders. -/
theorem p2m_continuousAt_besselYExp_order {h : ℂ} (hh : h ≠ 0) (z μ₀ : ℂ) :
    ContinuousAt (fun μ => besselYExp μ h z) μ₀ := by
  have hD := p2m_differentiable_besselDExp hh z
  by_cases hν : ∃ k : ℤ, μ₀ = k
  · obtain ⟨n, rfl⟩ := hν
    have hcont : ContinuousAt (fun μ => dslope (fun ν => p2m_besselDExp ν h z) n μ /
        dslope (fun ν : ℂ => Complex.sin (ν * π)) n μ) n :=
      (continuousAt_dslope_same.mpr (hD n)).div
        (continuousAt_dslope_same.mpr (by fun_prop)) (DLMF.Bessel.dslope_sin_ne_zero n
          (Metric.mem_ball_self (by norm_num)))
    refine hcont.congr ?_
    filter_upwards [Metric.ball_mem_nhds (n : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with μ hμ
    exact (p2m_besselYExp_eq_dslope n hμ hh z).symm
  · push Not at hν
    have hopen : IsOpen {μ : ℂ | Complex.sin (μ * π) ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hc : ContinuousAt (fun μ => p2m_besselDExp μ h z / Complex.sin (μ * π)) μ₀ :=
      (hD μ₀).continuousAt.div (by fun_prop) (DLMF.Bessel.sin_mul_pi_ne_zero hν)
    refine hc.congr ?_
    filter_upwards [hopen.mem_nhds (DLMF.Bessel.sin_mul_pi_ne_zero hν)] with μ hμ
    have hμ' : ∀ k : ℤ, μ ≠ k := fun k hk => hμ (by
      rw [hk]; exact DLMF.Bessel.sin_int_mul_pi_complex k)
    exact (p2m_besselYExp_of_not_int hμ' h z).symm

/-- The order recurrence of the continued `Y`, for every order. -/
theorem p2m_besselYExp_rec (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselYExp (μ - 1) h z + besselYExp (μ + 1) h z =
      2 * μ / (h * Complex.exp z) * besselYExp μ h z := by
  have hc := p2m_continuousAt_besselYExp_order hh z
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselYExp (μ - 1) h z + besselYExp (μ + 1) h z)
    (g := fun μ => 2 * μ / (h * Complex.exp z) * besselYExp μ h z)
    (((hc _).comp (by fun_prop : ContinuousAt (fun μ : ℂ => μ - 1) μ)).add
      ((hc _).comp (by fun_prop : ContinuousAt (fun μ : ℂ => μ + 1) μ)))
    ((by fun_prop : ContinuousAt (fun μ : ℂ => 2 * μ / (h * Complex.exp z)) μ).mul (hc μ))
    (fun c hc' => ?_)
  have hk := DLMF.Confluent.forall_of_mem_integerComplement hc'
  have hk1 : ∀ k : ℤ, c - 1 ≠ k := DLMF.Bessel.not_int_sub_one hk
  have hk2 : ∀ k : ℤ, c + 1 ≠ k := DLMF.Bessel.not_int_add_one hk
  rw [p2m_besselYExp_of_not_int hk, p2m_besselYExp_of_not_int hk1,
    p2m_besselYExp_of_not_int hk2]
  have hs := DLMF.Bessel.sin_mul_pi_ne_zero hk
  have r1 := p2m_besselJExp_rec c hh z
  have r2 := p2m_besselJExp_rec (-c) hh z
  rw [show -c - 1 = -(c + 1) by ring, show -c + 1 = -(c - 1) by ring] at r2
  simp only [p2m_besselDExp, DLMF.Bessel.cos_add_one_mul_pi, DLMF.Bessel.sin_add_one_mul_pi,
    DLMF.Bessel.cos_sub_one_mul_pi, DLMF.Bessel.sin_sub_one_mul_pi]
  have hez := Complex.exp_ne_zero z
  field_simp
  linear_combination (norm := (field_simp; ring)) (h * Complex.exp z * Complex.cos (c * π)) * r1 +
    (h * Complex.exp z) * r2

/-- Growth of a sequence with `‖a (n+2)‖ ≤ C (n+1) ‖a (n+1)‖ + ‖a n‖`, `C ≥ 1`:
`‖a n‖ ≤ E (2C)^n n!` with `E = max ‖a 0‖ ‖a 1‖`. -/
theorem p2m_growth_nat {a : ℕ → ℂ} {C : ℝ} (hC : 1 ≤ C)
    (ha : ∀ n : ℕ, ‖a (n + 2)‖ ≤ C * (n + 1) * ‖a (n + 1)‖ + ‖a n‖) (n : ℕ) :
    ‖a n‖ ≤ max ‖a 0‖ ‖a 1‖ * (2 * C) ^ n * n ! := by
  set E := max ‖a 0‖ ‖a 1‖
  have hE : 0 ≤ E := (norm_nonneg _).trans (le_max_left _ _)
  have key : ∀ n : ℕ, ‖a n‖ ≤ E * (2 * C) ^ n * n ! ∧
      ‖a (n + 1)‖ ≤ E * (2 * C) ^ (n + 1) * (n + 1) ! := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [E], ?_⟩
      simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
      calc ‖a 1‖ ≤ E := le_max_right _ _
        _ ≤ E * (2 * C) := le_mul_of_one_le_right hE (by linarith)
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := ha n
      have hf : ((n + 2) ! : ℝ) = (n + 2) * ((n + 1) * n !) := by
        push_cast [Nat.factorial_succ]; ring
      have hf1 : ((n + 1) ! : ℝ) = (n + 1) * n ! := by push_cast [Nat.factorial_succ]; ring
      rw [hf1] at ih
      rw [show n + 1 + 1 = n + 2 by ring, hf]
      have hn : (0 : ℝ) ≤ n ! := by positivity
      have hp : (0 : ℝ) ≤ (2 * C) ^ n := by positivity
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      calc ‖a (n + 2)‖ ≤ C * (n + 1) * ‖a (n + 1)‖ + ‖a n‖ := h1
        _ ≤ C * (n + 1) * (E * (2 * C) ^ (n + 1) * ((n + 1) * n !)) +
            E * (2 * C) ^ n * n ! := by
          gcongr
          · exact ih.2
          · exact ih.1
        _ ≤ E * (2 * C) ^ (n + 2) * ((n + 2) * ((n + 1) * n !)) := by
          have hEp : 0 ≤ E * (2 * C) ^ n * n ! := by positivity
          have : C * (n + 1) * (2 * C * (n + 1)) + 1 ≤ (2 * C) ^ 2 * ((n + 2) * (n + 1)) := by
            have hC2 : 1 ≤ C ^ 2 := by nlinarith
            have h3 : 3 ≤ ((n : ℝ) + 1) * (n + 3) := by nlinarith
            nlinarith [mul_le_mul hC2 h3 (by norm_num) (by positivity)]
          calc C * (n + 1) * (E * (2 * C) ^ (n + 1) * ((n + 1) * n !)) +
                E * (2 * C) ^ n * n ! =
                (E * (2 * C) ^ n * n !) * (C * (n + 1) * (2 * C * (n + 1)) + 1) := by ring
            _ ≤ (E * (2 * C) ^ n * n !) * ((2 * C) ^ 2 * ((n + 2) * (n + 1))) := by gcongr
            _ = _ := by ring
  exact (key n).1

/-- Growth of solutions of a three-term recurrence `u (k-1) + u (k+1) = (2(ν+k)/w) u k`:
`‖u k‖ ≤ E A^{|k|} |k|!`. -/
theorem p2m_growth_int {u : ℤ → ℂ} {ν w : ℂ} (hw : w ≠ 0)
    (hu : ∀ k : ℤ, u (k - 1) + u (k + 1) = 2 * (ν + k) / w * u k) :
    ∃ E A : ℝ, 0 ≤ E ∧ 0 ≤ A ∧ ∀ k : ℤ, ‖u k‖ ≤ E * A ^ k.natAbs * k.natAbs ! := by
  set C : ℝ := max 1 (2 * (‖ν‖ + 1) / ‖w‖)
  have hC : 1 ≤ C := le_max_left _ _
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hCn : ∀ (n : ℕ) (s : ℂ), ‖s‖ ≤ ‖ν‖ + n → 2 * ‖s‖ / ‖w‖ ≤ C * (n + 1) := by
    intro n s hs
    have h1 : 2 * (‖ν‖ + 1) / ‖w‖ ≤ C := le_max_right _ _
    have h2 : 2 * ‖s‖ / ‖w‖ ≤ 2 * (‖ν‖ + 1) / ‖w‖ * (n + 1) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hw'.le
      nlinarith [norm_nonneg ν, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc 2 * ‖s‖ / ‖w‖ ≤ 2 * (‖ν‖ + 1) / ‖w‖ * (n + 1) := h2
      _ ≤ C * (n + 1) := by gcongr
  have hstep : ∀ (k : ℤ) (n : ℕ), ‖ν + k‖ ≤ ‖ν‖ + n → ∀ x y : ℂ, x + y = 2 * (ν + k) / w * u k →
      ‖y‖ ≤ C * (n + 1) * ‖u k‖ + ‖x‖ := by
    intro k n hk x y hxy
    have : y = 2 * (ν + k) / w * u k - x := by linear_combination hxy
    rw [this]
    calc ‖2 * (ν + k) / w * u k - x‖ ≤ ‖2 * (ν + k) / w * u k‖ + ‖x‖ := norm_sub_le _ _
      _ = 2 * ‖ν + k‖ / ‖w‖ * ‖u k‖ + ‖x‖ := by
        rw [norm_mul, norm_div, norm_mul, Complex.norm_two]
      _ ≤ C * (n + 1) * ‖u k‖ + ‖x‖ := by gcongr; exact hCn n _ hk
  -- forward: a n = u (n - 1)
  have hf := p2m_growth_nat (a := fun n : ℕ => u ((n : ℤ) - 1)) hC (fun n => by
    have := hstep n n (by
      calc ‖ν + (n : ℤ)‖ ≤ ‖ν‖ + ‖((n : ℤ) : ℂ)‖ := norm_add_le _ _
        _ = ‖ν‖ + n := by simp) (u ((n : ℤ) - 1)) (u ((n : ℤ) + 1)) (hu n)
    convert this using 3 <;> push_cast <;> ring_nf)
  -- backward: b n = u (1 - n)
  have hb := p2m_growth_nat (a := fun n : ℕ => u (1 - (n : ℤ))) hC (fun n => by
    have := hstep (-(n : ℤ)) n (by
      calc ‖ν + ((-(n : ℤ) : ℤ) : ℂ)‖ ≤ ‖ν‖ + ‖((-(n : ℤ) : ℤ) : ℂ)‖ := norm_add_le _ _
        _ = ‖ν‖ + n := by simp) (u (-(n : ℤ) + 1)) (u (-(n : ℤ) - 1)) (by
          rw [add_comm]; exact hu (-(n : ℤ)))
    convert this using 3 <;> push_cast <;> ring_nf)
  set E₁ := max ‖u ((0 : ℕ) - 1 : ℤ)‖ ‖u ((1 : ℕ) - 1 : ℤ)‖
  set E₂ := max ‖u (1 - (0 : ℕ) : ℤ)‖ ‖u (1 - (1 : ℕ) : ℤ)‖
  refine ⟨max E₁ E₂ * (2 * C), 4 * C, by positivity, by positivity, fun k => ?_⟩
  have hfac : ∀ m : ℕ, ((m + 1) ! : ℝ) ≤ 2 ^ m * m ! := by
    intro m
    rw [Nat.factorial_succ]; push_cast
    have : (m : ℝ) + 1 ≤ 2 ^ m := by
      have : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
      exact_mod_cast this
    have hp : (0 : ℝ) ≤ (Nat.factorial m : ℝ) := by positivity
    nlinarith
  have hE1 : E₁ ≤ max E₁ E₂ := le_max_left _ _
  have hE2 : E₂ ≤ max E₁ E₂ := le_max_right _ _
  have hE0 : 0 ≤ E₁ := (norm_nonneg _).trans (le_max_left _ _)
  have hC2 : 0 ≤ 2 * C := by linarith
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · have := hf (m + 1)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at this
    simp only [Int.natAbs_natCast]
    calc ‖u m‖ ≤ E₁ * (2 * C) ^ (m + 1) * (m + 1) ! := this
      _ ≤ max E₁ E₂ * (2 * C) ^ (m + 1) * (2 ^ m * m !) := by gcongr; exact hfac m
      _ = _ := by
        have h4 : (2 : ℝ) ^ (m * 2) = 4 ^ m := by rw [pow_mul']; norm_num
        ring_nf; rw [h4]
  · have := hb (m + 1)
    rw [show (1 : ℤ) - ((m + 1 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring] at this
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    have hE0' : 0 ≤ E₂ := (norm_nonneg _).trans (le_max_left _ _)
    calc ‖u (-(m : ℤ))‖ ≤ E₂ * (2 * C) ^ (m + 1) * (m + 1) ! := this
      _ ≤ max E₁ E₂ * (2 * C) ^ (m + 1) * (2 ^ m * m !) := by gcongr; exact hfac m
      _ = _ := by
        have h4 : (2 : ℝ) ^ (m * 2) = 4 ^ m := by rw [pow_mul']; norm_num
        ring_nf; rw [h4]

/-- A bounded solution of `q u_{n+1} - D_n u_n + q u_{n-1} = 0` with `‖D_n‖ ≥ 2n² + 3‖q‖`
for `n ≥ N₀` decays like `K^n / (n!)²`. -/
lemma p2m_decay_nat {u : ℕ → ℂ} {D : ℕ → ℂ} {q : ℂ} {M : ℝ} (hq : q ≠ 0)
    (hM : ∀ n, ‖u n‖ ≤ M) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hD : ∀ n, N₀ ≤ n → 2 * (n : ℝ) ^ 2 + 3 * ‖q‖ ≤ ‖D n‖)
    (hrec : ∀ n, 1 ≤ n → q * u (n + 1) - D n * u n + q * u (n - 1) = 0) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ n, ‖u n‖ * (n ! : ℝ) ^ 2 ≤ C * K ^ n := by
  have hq0 : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the recurrence solved for `u (n+1)`
  have hlow : ∀ n, N₀ ≤ n → ‖u (n - 1)‖ < ‖u n‖ → 2 * ‖u n‖ < ‖u (n + 1)‖ := by
    intro n hn hlt
    have h1 : q * u (n + 1) = D n * u n - q * u (n - 1) := by
      linear_combination hrec n (by omega)
    have h2 : ‖D n * u n‖ - ‖q * u (n - 1)‖ ≤ ‖q * u (n + 1)‖ := by
      rw [h1]; exact norm_sub_norm_le _ _
    rw [norm_mul, norm_mul, norm_mul] at h2
    have h3 : 3 * ‖q‖ * ‖u n‖ ≤ ‖D n‖ * ‖u n‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have := hD n hn; nlinarith [sq_nonneg (n : ℝ)]
    have h4 : ‖q‖ * ‖u (n - 1)‖ < ‖q‖ * ‖u n‖ := mul_lt_mul_of_pos_left hlt hq0
    have : ‖q‖ * (2 * ‖u n‖) < ‖q‖ * ‖u (n + 1)‖ := by nlinarith
    exact lt_of_mul_lt_mul_left this hq0.le
  -- eventual monotonicity
  have hmono : ∀ n, N₀ ≤ n → ‖u (n + 1)‖ ≤ ‖u n‖ := by
    intro n hn
    by_contra hcon
    push Not at hcon
    have key : ∀ i : ℕ, ‖u (n + i)‖ < ‖u (n + i + 1)‖ ∧
        2 ^ i * ‖u (n + 1)‖ ≤ ‖u (n + 1 + i)‖ := by
      intro i
      induction i with
      | zero => exact ⟨by simpa using hcon, by simp⟩
      | succ i ih =>
        have hh := hlow (n + i + 1) (by omega) (by simpa using ih.1)
        refine ⟨by
          rw [show n + (i + 1) = n + i + 1 by ring]; linarith [norm_nonneg (u (n + i + 1))], ?_⟩
        rw [pow_succ, show n + 1 + (i + 1) = n + i + 1 + 1 by ring]
        have := ih.2
        rw [show n + 1 + i = n + i + 1 by ring] at this
        nlinarith
    have hpos : 0 < ‖u (n + 1)‖ := lt_of_le_of_lt (norm_nonneg _) hcon
    obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (M / ‖u (n + 1)‖) (by norm_num : (1 : ℝ) < 2)
    have := (key i).2.trans (hM _)
    rw [div_lt_iff₀ hpos] at hi
    linarith
  -- the ratio bound
  have hratio : ∀ n, N₀ + 1 ≤ n → ‖u n‖ * (n : ℝ) ^ 2 ≤ ‖q‖ * ‖u (n - 1)‖ := by
    intro n hn
    have h1 : D n * u n = q * (u (n + 1) + u (n - 1)) := by
      linear_combination -(hrec n (by omega))
    have h2 : ‖D n‖ * ‖u n‖ ≤ ‖q‖ * (‖u (n + 1)‖ + ‖u (n - 1)‖) := by
      rw [← norm_mul, h1, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    have m1 := hmono n (by omega)
    have m2 := hmono (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at m2
    have h3 : 2 * (n : ℝ) ^ 2 * ‖u n‖ ≤ ‖D n‖ * ‖u n‖ :=
      mul_le_mul_of_nonneg_right (by linarith [hD n (by omega)]) (norm_nonneg _)
    nlinarith
  set K : ℝ := max 1 ‖q‖
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKq : ‖q‖ ≤ K := le_max_right _ _
  refine ⟨M * (N₀ ! : ℝ) ^ 2, K, by positivity, by positivity, fun n => ?_⟩
  rcases le_or_gt N₀ n with hn | hn
  · induction n, hn using Nat.le_induction with
    | base =>
      calc ‖u N₀‖ * (N₀ ! : ℝ) ^ 2 ≤ M * (N₀ ! : ℝ) ^ 2 := by gcongr; exact hM _
        _ ≤ M * (N₀ ! : ℝ) ^ 2 * K ^ N₀ := le_mul_of_one_le_right (by positivity)
            (one_le_pow₀ hK1)
    | succ n hn ih =>
      have hr := hratio (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hr
      have hf : ((n + 1) ! : ℝ) = (n + 1) * n ! := by push_cast [Nat.factorial_succ]; ring
      rw [hf, pow_succ]
      push_cast at hr
      calc ‖u (n + 1)‖ * (((n : ℝ) + 1) * n !) ^ 2 = (‖u (n + 1)‖ * ((n : ℝ) + 1) ^ 2) *
            (n ! : ℝ) ^ 2 := by ring
        _ ≤ (‖q‖ * ‖u n‖) * (n ! : ℝ) ^ 2 := by gcongr
        _ = ‖q‖ * (‖u n‖ * (n ! : ℝ) ^ 2) := by ring
        _ ≤ K * (M * (N₀ ! : ℝ) ^ 2 * K ^ n) := by gcongr
        _ = _ := by ring
  · calc ‖u n‖ * (n ! : ℝ) ^ 2 ≤ M * (N₀ ! : ℝ) ^ 2 := by
          gcongr
          · exact hM n
      _ ≤ M * (N₀ ! : ℝ) ^ 2 * K ^ n := le_mul_of_one_le_right (by positivity)
            (one_le_pow₀ hK1)

/-- A bounded solution `c : ℤ → ℂ` of the recurrence 28.14.4 with `q ≠ 0` satisfies
`‖c_m‖ (|m|!)² ≤ C K^{|m|}`. -/
theorem p2m_decay_int {c : ℤ → ℂ} {ν q a : ℂ} {M : ℝ} (hq : q ≠ 0) (hM : ∀ m, ‖c m‖ ≤ M)
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ C * K ^ m.natAbs := by
  obtain ⟨N₁, hN₁⟩ := p1b_norm_D_ge ν a (3 * ‖q‖)
  obtain ⟨N₂, hN₂⟩ := p1b_norm_D_ge (-ν) a (3 * ‖q‖)
  obtain ⟨C₁, K₁, hC₁, hK₁, h₁⟩ := p2m_decay_nat (u := fun n : ℕ => c n)
    (D := fun n : ℕ => a - (ν + 2 * (n : ℤ)) ^ 2) hq (fun n => hM n) (max N₁ 1)
    (le_max_right _ _) (fun n hn => by
      have := hN₁ n (by exact_mod_cast (le_max_left _ _).trans hn)
      simpa using this)
    (fun n hn => by
      have := hrec n
      rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by omega]
      push_cast at this ⊢
      exact this)
  obtain ⟨C₂, K₂, hC₂, hK₂, h₂⟩ := p2m_decay_nat (u := fun n : ℕ => c (-(n : ℤ)))
    (D := fun n : ℕ => a - (-ν + 2 * (n : ℤ)) ^ 2) hq (fun n => hM _) (max N₂ 1)
    (le_max_right _ _) (fun n hn => by
      have := hN₂ n (by exact_mod_cast (le_max_left _ _).trans hn)
      simpa using this)
    (fun n hn => by
      have := hrec (-(n : ℤ))
      rw [show -((n - 1 : ℕ) : ℤ) = -(n : ℤ) + 1 by omega,
        show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by omega]
      push_cast at this ⊢
      linear_combination this)
  refine ⟨max C₁ C₂, max K₁ K₂, by positivity, by positivity, fun m => ?_⟩
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · simp only [Int.natAbs_natCast]
    calc ‖c n‖ * (n ! : ℝ) ^ 2 ≤ C₁ * K₁ ^ n := h₁ n
      _ ≤ max C₁ C₂ * max K₁ K₂ ^ n := by gcongr <;> simp
  · simp only [Int.natAbs_neg, Int.natAbs_natCast]
    calc ‖c (-(n : ℤ))‖ * (n ! : ℝ) ^ 2 ≤ C₂ * K₂ ^ n := h₂ n
      _ ≤ max C₁ C₂ * max K₁ K₂ ^ n := by gcongr <;> simp

/-- `R^{|ℓ|} / |ℓ|!` is summable over `ℤ`. -/
theorem p2m_summable_pow_div_factorial_int (R : ℝ) :
    Summable (fun ℓ : ℤ => R ^ ℓ.natAbs / (ℓ.natAbs ! : ℝ)) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using Real.summable_pow_div_factorial R
  · simpa using Real.summable_pow_div_factorial R

/-- `(a + b)! ≤ 2^{a+b} a! b!`. -/
lemma p2m_factorial_add_le (a b : ℕ) : ((a + b) ! : ℝ) ≤ 2 ^ (a + b) * a ! * b ! := by
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  have h2 := Nat.choose_le_two_pow (a + b) b
  have : (a + b) ! ≤ 2 ^ (a + b) * a ! * b ! := by
    rw [← h, mul_assoc, mul_assoc, mul_comm (a !)]
    exact Nat.mul_le_mul_right _ h2
  exact_mod_cast this

/-- The terms `(-1)^ℓ c_ℓ J_{ℓ+α} 𝒞_{β+ℓ}` of the cross-product series. -/
def p2m_fam (c Jx Cy : ℤ → ℂ) (α β ℓ : ℤ) : ℂ :=
  (-1 : ℂ) ^ ℓ * c ℓ * Jx (ℓ + α) * Cy (β + ℓ)

/-- The common bound for the cross-product terms. -/
theorem p2m_fam_bound {c Jx Cy : ℤ → ℂ} {Cc K EJ B EC A : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hEJ : 0 ≤ EJ) (hB : 1 ≤ B) (hEC : 0 ≤ EC) (hA : 1 ≤ A)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs)
    (hJ : ∀ k : ℤ, ‖Jx k‖ ≤ EJ * B ^ k.natAbs)
    (hC : ∀ k : ℤ, ‖Cy k‖ ≤ EC * A ^ k.natAbs * (k.natAbs ! : ℝ)) (α β ℓ : ℤ) :
    ‖p2m_fam c Jx Cy α β ℓ‖ ≤ (Cc * EJ * EC * B ^ α.natAbs * (2 * A) ^ β.natAbs *
      (β.natAbs ! : ℝ)) * ((2 * K * B * A) ^ ℓ.natAbs / (ℓ.natAbs ! : ℝ)) := by
  set n := ℓ.natAbs
  have hn : (0 : ℝ) < n ! := by positivity
  have hc' : ‖c ℓ‖ ≤ Cc * K ^ n / ((n ! : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hc ℓ
  have hJ' : ‖Jx (ℓ + α)‖ ≤ EJ * (B ^ n * B ^ α.natAbs) := by
    refine (hJ _).trans ?_
    rw [← pow_add]
    gcongr
    exact Int.natAbs_add_le _ _
  have hC' : ‖Cy (β + ℓ)‖ ≤ EC * (A ^ β.natAbs * A ^ n) *
      (2 ^ (β.natAbs + n) * β.natAbs ! * n !) := by
    refine (hC _).trans ?_
    have hle : (β + ℓ).natAbs ≤ β.natAbs + n := Int.natAbs_add_le _ _
    rw [← pow_add]
    gcongr
    exact (Nat.cast_le.mpr (Nat.factorial_le hle)).trans (p2m_factorial_add_le _ _)
  have hs : ‖(-1 : ℂ) ^ ℓ‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  rw [p2m_fam, norm_mul, norm_mul, norm_mul, hs, one_mul]
  calc ‖c ℓ‖ * ‖Jx (ℓ + α)‖ * ‖Cy (β + ℓ)‖ ≤ (Cc * K ^ n / ((n ! : ℝ) ^ 2)) *
        (EJ * (B ^ n * B ^ α.natAbs)) * (EC * (A ^ β.natAbs * A ^ n) *
          (2 ^ (β.natAbs + n) * β.natAbs ! * n !)) := by
        gcongr
    _ = _ := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add]
        field_simp

lemma p2m_fam_summable {c Jx Cy : ℤ → ℂ} {Cc K EJ B EC A : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hEJ : 0 ≤ EJ) (hB : 1 ≤ B) (hEC : 0 ≤ EC) (hA : 1 ≤ A)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs)
    (hJ : ∀ k : ℤ, ‖Jx k‖ ≤ EJ * B ^ k.natAbs)
    (hC : ∀ k : ℤ, ‖Cy k‖ ≤ EC * A ^ k.natAbs * (k.natAbs ! : ℝ)) (α β : ℤ) :
    Summable (p2m_fam c Jx Cy α β) :=
  Summable.of_norm_bounded (((p2m_summable_pow_div_factorial_int _).mul_left _))
    (fun ℓ => p2m_fam_bound hCc hK hEJ hB hEC hA hc hJ hC α β ℓ)

theorem p2m_fam_tsum_le {c Jx Cy : ℤ → ℂ} {Cc K EJ B EC A : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hEJ : 0 ≤ EJ) (hB : 1 ≤ B) (hEC : 0 ≤ EC) (hA : 1 ≤ A)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs)
    (hJ : ∀ k : ℤ, ‖Jx k‖ ≤ EJ * B ^ k.natAbs)
    (hC : ∀ k : ℤ, ‖Cy k‖ ≤ EC * A ^ k.natAbs * (k.natAbs ! : ℝ)) (α β : ℤ) :
    ‖∑' ℓ, p2m_fam c Jx Cy α β ℓ‖ ≤ (Cc * EJ * EC * B ^ α.natAbs * (2 * A) ^ β.natAbs *
      (β.natAbs ! : ℝ)) * ∑' ℓ : ℤ, (2 * K * B * A) ^ ℓ.natAbs / (ℓ.natAbs ! : ℝ) := by
  have hs := p2m_summable_pow_div_factorial_int (2 * K * B * A)
  rw [← tsum_mul_left]
  refine tsum_of_norm_bounded (hs.mul_left _).hasSum
    (fun ℓ => p2m_fam_bound hCc hK hEJ hB hEC hA hc hJ hC α β ℓ)



/-- The pointwise identity behind the recurrence in `n` of the cross-product series. -/
lemma p2m_fam_identity {c Jx Cy : ℤ → ℂ} {ν a x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrec : ∀ m : ℤ, x * y * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + x * y * c (m - 1) = 0)
    (hJr : ∀ k : ℤ, Jx (k - 1) + Jx (k + 1) = 2 * k / x * Jx k)
    (hCr : ∀ k : ℤ, Cy (k - 1) + Cy (k + 1) = 2 * (ν + k) / y * Cy k) (n ℓ : ℤ) :
    (a - (ν + 2 * n) ^ 2) * p2m_fam c Jx Cy (-n) n ℓ =
      x * y * p2m_fam c Jx Cy (-(n + 1)) (n + 1) ℓ + x * y * p2m_fam c Jx Cy (-(n - 1)) (n - 1) ℓ +
      x * y * p2m_fam c Jx Cy (-n - 1) (n - 1) ℓ + x * y * p2m_fam c Jx Cy (-n + 1) (n + 1) ℓ -
      x * y * p2m_fam c Jx Cy (-n - 1) (n - 1) (ℓ + 1) -
      x * y * p2m_fam c Jx Cy (-n + 1) (n + 1) (ℓ - 1) := by
  have eJ := hJr (ℓ - n)
  have eC := hCr (n + ℓ)
  have ec := hrec ℓ
  simp only [p2m_fam]
  rw [show ℓ + -(n + 1) = ℓ - n - 1 by ring, show ℓ + -(n - 1) = ℓ - n + 1 by ring,
    show ℓ + (-n - 1) = ℓ - n - 1 by ring, show ℓ + (-n + 1) = ℓ - n + 1 by ring,
    show ℓ + 1 + (-n - 1) = ℓ - n by ring, show ℓ - 1 + (-n + 1) = ℓ - n by ring,
    show n + 1 + ℓ = n + ℓ + 1 by ring, show n - 1 + ℓ = n + ℓ - 1 by ring,
    show n - 1 + (ℓ + 1) = n + ℓ by ring, show n + 1 + (ℓ - 1) = n + ℓ by ring,
    show ℓ + -n = ℓ - n by ring, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  push_cast at eJ eC ec ⊢
  linear_combination (norm := (field_simp; ring))
    (-(x * y) * (-1 : ℂ) ^ ℓ * c ℓ * (Cy (n + ℓ - 1) + Cy (n + ℓ + 1))) * eJ +
    (-(x * y) * (-1 : ℂ) ^ ℓ * c ℓ * (2 * (ℓ - n) / x * Jx (ℓ - n))) * eC +
    (-(-1 : ℂ) ^ ℓ * Jx (ℓ - n) * Cy (n + ℓ)) * ec



/-- Two consecutive zeros of a solution of the three-term recurrence force it to vanish. -/
lemma p2m_rec_eq_zero {u : ℤ → ℂ} {D : ℤ → ℂ} {q : ℂ} (hq : q ≠ 0)
    (hrec : ∀ m : ℤ, q * u (m + 1) - D m * u m + q * u (m - 1) = 0) {n₀ : ℤ}
    (h0 : u n₀ = 0) (h1 : u (n₀ + 1) = 0) (m : ℤ) : u m = 0 := by
  have key : ∀ k : ℤ, u k = 0 ∧ u (k + 1) = 0 := by
    intro k
    induction k using Int.inductionOn' with
    | b => exact n₀
    | zero => exact ⟨h0, h1⟩
    | succ k _ ih =>
      refine ⟨ih.2, ?_⟩
      have := hrec (k + 1)
      rw [ih.2, show k + 1 - 1 = k by ring, ih.1] at this
      simpa [hq] using this
    | pred k _ ih =>
      refine ⟨?_, by rw [show k - 1 + 1 = k by ring]; exact ih.1⟩
      have := hrec k
      rw [ih.1, ih.2] at this
      simpa [hq] using this
  exact (key m).1

/-- **Abstract cross-product theorem**: the series `S_n = ∑_ℓ (-1)^ℓ c_ℓ J_{ℓ-n} 𝒞_{n+ℓ}` built
from a bounded solution `c` of the recurrence 28.14.4 (with `q = xy ≠ 0`) and solutions of the
Bessel order recurrences in `x` and `y` with the stated growth satisfy `S_n = L c_n`. -/
theorem p2m_cross_series {c Jx Cy : ℤ → ℂ} {ν a x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrec : ∀ m : ℤ, x * y * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + x * y * c (m - 1) = 0)
    (hJr : ∀ k : ℤ, Jx (k - 1) + Jx (k + 1) = 2 * k / x * Jx k)
    (hCr : ∀ k : ℤ, Cy (k - 1) + Cy (k + 1) = 2 * (ν + k) / y * Cy k)
    {Cc K EJ B EC A : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hEJ : 0 ≤ EJ) (hB : 1 ≤ B) (hEC : 0 ≤ EC) (hA : 1 ≤ A)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs)
    (hJ : ∀ k : ℤ, ‖Jx k‖ ≤ EJ * B ^ k.natAbs)
    (hC : ∀ k : ℤ, ‖Cy k‖ ≤ EC * A ^ k.natAbs * (k.natAbs ! : ℝ)) {n₀ : ℤ} (hn₀ : c n₀ ≠ 0)
    (n : ℤ) :
    HasSum (p2m_fam c Jx Cy (-n) n)
      (c n * ((c n₀)⁻¹ * ∑' ℓ, p2m_fam c Jx Cy (-n₀) n₀ ℓ)) := by
  have hq : x * y ≠ 0 := mul_ne_zero hx hy
  have hsum := p2m_fam_summable hCc hK hEJ hB hEC hA hc hJ hC
  set S : ℤ → ℂ := fun n => ∑' ℓ, p2m_fam c Jx Cy (-n) n ℓ with hSdef
  -- the recurrence in `n`
  have hSrec : ∀ m : ℤ, x * y * S (m + 1) - (a - (ν + 2 * m) ^ 2) * S m +
      x * y * S (m - 1) = 0 := by
    intro m
    have h1 := (hsum (-(m + 1)) (m + 1)).hasSum.mul_left (x * y)
    have h2 := (hsum (-(m - 1)) (m - 1)).hasSum.mul_left (x * y)
    have h3 := (hsum (-m - 1) (m - 1)).hasSum.mul_left (x * y)
    have h4 := (hsum (-m + 1) (m + 1)).hasSum.mul_left (x * y)
    have h5 := ((Equiv.addRight (1 : ℤ)).hasSum_iff.mpr (hsum (-m - 1) (m - 1)).hasSum).mul_left
      (x * y)
    have h6 := ((Equiv.addRight (-1 : ℤ)).hasSum_iff.mpr (hsum (-m + 1) (m + 1)).hasSum).mul_left
      (x * y)
    have htot := ((((h1.add h2).add h3).add h4).sub h5).sub h6
    have hL := (hsum (-m) m).hasSum.mul_left (a - (ν + 2 * m) ^ 2)
    have e : (fun ℓ => (a - (ν + 2 * m) ^ 2) * p2m_fam c Jx Cy (-m) m ℓ) = fun ℓ =>
        x * y * p2m_fam c Jx Cy (-(m + 1)) (m + 1) ℓ +
          x * y * p2m_fam c Jx Cy (-(m - 1)) (m - 1) ℓ +
          x * y * p2m_fam c Jx Cy (-m - 1) (m - 1) ℓ + x * y * p2m_fam c Jx Cy (-m + 1) (m + 1) ℓ -
          x * y * (p2m_fam c Jx Cy (-m - 1) (m - 1) ∘ Equiv.addRight 1) ℓ -
          x * y * (p2m_fam c Jx Cy (-m + 1) (m + 1) ∘ Equiv.addRight (-1)) ℓ := by
      funext ℓ
      rw [p2m_fam_identity hx hy hrec hJr hCr m ℓ]
      simp [sub_eq_add_neg]
    rw [e] at hL
    have := hL.unique htot
    simp only [hSdef]
    linear_combination -this
  -- growth of `S`
  set Sig : ℝ := ∑' ℓ : ℤ, (2 * K * B * A) ^ ℓ.natAbs / (ℓ.natAbs ! : ℝ)
  have hSig : 0 ≤ Sig := tsum_nonneg fun ℓ => by positivity
  set G : ℝ := Cc * EJ * EC * Sig
  have hG : 0 ≤ G := by positivity
  have hSb : ∀ m : ℤ, ‖S m‖ ≤ G * (2 * A * B) ^ m.natAbs * (m.natAbs ! : ℝ) := by
    intro m
    have := p2m_fam_tsum_le hCc hK hEJ hB hEC hA hc hJ hC (-m) m
    rw [Int.natAbs_neg] at this
    calc ‖S m‖ ≤ _ := this
      _ = _ := by rw [mul_pow]; ring
  -- the Casoratian
  set W : ℤ → ℂ := fun m => S m * c (m + 1) - S (m + 1) * c m
  have hWstep : ∀ m : ℤ, W (m + 1) = W m := by
    intro m
    have e1 := hSrec (m + 1)
    have e2 := hrec (m + 1)
    simp only [W]
    rw [show m + 1 - 1 = m by ring] at e1 e2
    apply mul_left_cancel₀ hq
    linear_combination (-c (m + 1)) * e1 + S (m + 1) * e2
  have hWconst : ∀ m : ℤ, W m = W 0 := by
    intro m
    induction m using Int.inductionOn' with
    | b => exact 0
    | zero => rfl
    | succ k _ ih => rw [hWstep, ih]
    | pred k _ ih => rw [← ih, ← hWstep (k - 1), sub_add_cancel]
  have hW0 : W 0 = 0 := by
    set X : ℝ := 2 * A * B
    have hX : 0 ≤ X := by positivity
    have hbound : ∀ m : ℕ, ‖W 0‖ ≤ G * Cc * (K + X) * (2 * X * K) ^ m / (m ! : ℝ) := by
      intro m
      rw [← hWconst m]
      have hcm := hc m
      have hcm1 := hc (m + 1)
      have hSm := hSb m
      have hSm1 := hSb (m + 1)
      simp only [Int.natAbs_natCast] at hcm hSm
      rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
        at hcm1 hSm1
      have hf : ((m + 1) ! : ℝ) = (m + 1) * m ! := by push_cast [Nat.factorial_succ]; ring
      rw [hf] at hcm1 hSm1
      have hm0 : (0 : ℝ) < m ! := by positivity
      have hm1 : (m : ℝ) + 1 ≤ 2 ^ m := by
        have : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
        exact_mod_cast this
      simp only [W]
      rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring]
      calc ‖S m * c (m + 1 : ℕ) - S (m + 1 : ℕ) * c m‖ ≤
            ‖S m‖ * ‖c (m + 1 : ℕ)‖ + ‖S (m + 1 : ℕ)‖ * ‖c m‖ := by
            rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
        _ ≤ (G * X ^ m * m !) * (Cc * K ^ (m + 1) / (((m : ℝ) + 1) * m !) ^ 2) +
            (G * X ^ (m + 1) * ((m + 1) * m !)) * (Cc * K ^ m / (m ! : ℝ) ^ 2) := by
            gcongr
            · rw [le_div_iff₀ (by positivity)]; exact hcm1
            · rw [le_div_iff₀ (by positivity)]; exact hcm
        _ = (G * Cc * (X * K) ^ m / (m ! : ℝ)) * (K / ((m : ℝ) + 1) ^ 2 + X * (m + 1)) := by
            field_simp; ring
        _ ≤ (G * Cc * (X * K) ^ m / (m ! : ℝ)) * ((K + X) * 2 ^ m) := by
            have hK1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
              nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
            have h1 : K / ((m : ℝ) + 1) ^ 2 ≤ K := div_le_self hK hK1
            have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
            gcongr
            nlinarith
        _ = G * Cc * (K + X) * (2 * X * K) ^ m / (m ! : ℝ) := by
            rw [show (2 * X * K) ^ m = 2 ^ m * (X * K) ^ m by rw [← mul_pow]; ring]; ring
    have ht : Tendsto (fun m : ℕ => G * Cc * (K + X) * (2 * X * K) ^ m / (m ! : ℝ)) atTop
        (𝓝 0) := by
      have := (FloorSemiring.tendsto_pow_div_factorial_atTop (2 * X * K)).const_mul
        (G * Cc * (K + X))
      simpa [mul_div_assoc] using this
    exact norm_le_zero_iff.mp (ge_of_tendsto' ht hbound)
  -- conclusion
  set L : ℂ := (c n₀)⁻¹ * S n₀
  have hu := p2m_rec_eq_zero (u := fun m => S m - L * c m) (D := fun m => a - (ν + 2 * m) ^ 2) hq
    (fun m => by linear_combination hSrec m - L * hrec m) (n₀ := n₀)
    (by simp only [L]; field_simp; ring)
    (by
      have h := hWconst n₀
      rw [hW0] at h
      simp only [W] at h
      simp only [L]
      field_simp
      linear_combination -h) n
  have : S n = c n * L := by linear_combination hu
  rw [← this]
  exact (hsum (-n) n).hasSum

end DLMF.Mathieu
