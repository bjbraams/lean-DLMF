/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.Mathieu.Basic.ContinuedFractions
public import DLMF.Mathieu.P3qCeSe
public import DLMF.Mathieu.P3qCeSeGen
public import DLMF.Mathieu.SpectralExistence

/-!
# Expansions for small `q` (DLMF §28.6)

The power series 28.6.1–28.6.14 of the eigenvalues `a_n(q)`, `b_n(q)` and 28.6.21–28.6.26 of
`ce_n`, `se_n` converge for small `|q|`; DLMF gives their leading terms. They are stated here as
`Asymptotics.IsBigO` statements as `q → 0` (real `q`), with the remainder of the order of the
first omitted power. All coefficients were checked numerically (eigenvalues of the
tridiagonal recurrence matrices of 28.4.5–28.4.8 at 40 digits).

**Proofs of 28.6.1–28.6.13.** Each expansion is proved by the eigenvalue perturbation estimate
`p3q_eig_isBigO` of `DLMF.Mathieu.P3qJacobi` applied to the Fourier recurrence of the class
(`p3q_eig_AE`, `p3q_eig_AO`, `p3q_eig_BO`, `p3q_eig_BE` of `DLMF.Mathieu.P3qSpectrum`): the
trial vector is the Rayleigh–Schrödinger series of the Fourier coefficients (normalized
`A_n = 1`), truncated in row `i` below the power `q^{K - |i - n|}`, and the residual identities
are checked by `ring`. The trial vectors were generated with exact rational arithmetic; the
computed eigenvalue coefficients agree with all printed coefficients of 28.6.1–28.6.13.
28.6.14 (general `m ≥ 7`) uses a trial vector rational in `m` (`DLMF.Mathieu.P3qGeneral`).
The function expansions 28.6.21–28.6.26 use the eigenvector estimate and normalization
argument `p3q_expand` of `DLMF.Mathieu.P3qVector`, with explicit trial vectors in
`DLMF.Mathieu.P3qCeSe` (small `m`) and `DLMF.Mathieu.P3qCeSeGen` (`m ≥ 6`).

**Check (28.6.12, 28.6.13).** The coefficients of `q⁶` in `a₆(q)` and `b₆(q)` are
`6743617/92935987200000` and `-5861633/92935987200000`, as DLMF prints them (with the digit
grouping `9293 59872 00000`). Numerically
`(a₆(q) - 36 - q²/70 - 187q⁴/43904000)/q⁶ → 7.2562…·10⁻⁸`, and with the corrected values
`a₆ - b₆ = q⁶/7372800 + O(q⁸)`, which is 28.6.15 for `m = 6`, while `(a₆ + b₆)/2` matches
the general formula 28.6.14 at `m = 6`.

**Remark (28.6.16, `n = 0`).** For `n = 0` the left side of 28.6.16 reduces to `a`, and the
relation needs a factor 2: `a₀ = -2q²/(4 - a₀ - q²/(16 - a₀ - ⋯))`; it is stated separately.

The radii of convergence of Table 28.6.1 are numerical (excluded); the conjecture that they grow
like `n²` is not acquired; 28.6.20 is stated in terms of analytic continuation to discs.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- **DLMF 28.6.1**: `a₀(q) = -q²/2 + 7q⁴/128 - 29q⁶/2304 + 68687q⁸/18874368 + O(q¹⁰)`. -/
@[dlmf 28.6.E1]
theorem mathieuA_zero_small_q :
    (fun q : ℝ => mathieuA 0 q - (-(1 / 2) * q ^ 2 + 7 / 128 * q ^ 4 - 29 / 2304 * q ^ 6 +
      68687 / 18874368 * q ^ 8)) =O[𝓝 0] (fun q => q ^ 10) := by
  refine p3q_real_of_complex (p3q_eig_AE 0 (N := 10) (K := 10)
    (p := fun q : ℝ => -((1 : ℂ) / 2) * (q : ℂ) ^ 2 + ((7 : ℂ) / 128) * (q : ℂ) ^ 4
      - ((29 : ℂ) / 2304) * (q : ℂ) ^ 6 + ((68687 : ℂ) / 18874368) * (q : ℂ) ^ 8)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 2) * (q : ℂ) + ((7 : ℂ) / 128) * (q : ℂ) ^ 3
          - ((29 : ℂ) / 2304) * (q : ℂ) ^ 5 + ((68687 : ℂ) / 18874368) * (q : ℂ) ^ 7
      | 2 => ((1 : ℂ) / 32) * (q : ℂ) ^ 2 - ((5 : ℂ) / 1152) * (q : ℂ) ^ 4
          + ((4817 : ℂ) / 4718592) * (q : ℂ) ^ 6
      | 3 => -((1 : ℂ) / 1152) * (q : ℂ) ^ 3 + ((13 : ℂ) / 98304) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 73728) * (q : ℂ) ^ 4
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 5 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 10) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 9) (by decide)
          (s := fun q : ℝ => ((10519 : ℂ) / 2097152) - ((6049649 : ℂ) / 10871635968) * (q : ℂ) ^ 2
            + ((1991923 : ℂ) / 21743271936) * (q : ℂ) ^ 4
            - ((4717903969 : ℂ) / 356241767399424) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => ((10025 : ℂ) / 2097152) - ((609307 : ℂ) / 2717908992) * (q : ℂ) ^ 2
            + ((207607 : ℂ) / 7247757312) * (q : ℂ) ^ 4
            - ((330865279 : ℂ) / 89060441849856) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((5353 : ℂ) / 4718592) - ((6169 : ℂ) / 339738624) * (q : ℂ) ^ 2
            + ((104879 : ℂ) / 21743271936) * (q : ℂ) ^ 4
            - ((892931 : ℂ) / 1855425871872) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => ((41 : ℂ) / 294912) - ((7 : ℂ) / 9437184) * (q : ℂ) ^ 2
            + ((29 : ℂ) / 169869312) * (q : ℂ) ^ 4 - ((68687 : ℂ) / 1391569403904) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 73728))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.2**: `a₁(q) = 1 + q - q²/8 - q³/64 - q⁴/1536 + 11q⁵/36864 + 49q⁶/589824
+ 55q⁷/9437184 - 83q⁸/35389440 + O(q⁹)`. -/
@[dlmf 28.6.E2]
theorem mathieuA_one_small_q :
    (fun q : ℝ => mathieuA 1 q - (1 + q - 1 / 8 * q ^ 2 - 1 / 64 * q ^ 3 - 1 / 1536 * q ^ 4 +
      11 / 36864 * q ^ 5 + 49 / 589824 * q ^ 6 + 55 / 9437184 * q ^ 7 -
      83 / 35389440 * q ^ 8)) =O[𝓝 0] (fun q => q ^ 9) := by
  refine p3q_real_of_complex (p3q_eig_AO 0 (N := 9) (K := 9)
    (p := fun q : ℝ => (1 : ℂ) + (1 : ℂ) * (q : ℂ) - ((1 : ℂ) / 8) * (q : ℂ) ^ 2
      - ((1 : ℂ) / 64) * (q : ℂ) ^ 3 - ((1 : ℂ) / 1536) * (q : ℂ) ^ 4
      + ((11 : ℂ) / 36864) * (q : ℂ) ^ 5 + ((49 : ℂ) / 589824) * (q : ℂ) ^ 6
      + ((55 : ℂ) / 9437184) * (q : ℂ) ^ 7 - ((83 : ℂ) / 35389440) * (q : ℂ) ^ 8)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 8) * (q : ℂ) - ((1 : ℂ) / 64) * (q : ℂ) ^ 2
          - ((1 : ℂ) / 1536) * (q : ℂ) ^ 3 + ((11 : ℂ) / 36864) * (q : ℂ) ^ 4
          + ((49 : ℂ) / 589824) * (q : ℂ) ^ 5 + ((55 : ℂ) / 9437184) * (q : ℂ) ^ 6
          - ((83 : ℂ) / 35389440) * (q : ℂ) ^ 7
      | 2 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1152) * (q : ℂ) ^ 3
          + ((1 : ℂ) / 24576) * (q : ℂ) ^ 4 - ((7 : ℂ) / 393216) * (q : ℂ) ^ 5
          - ((719 : ℂ) / 141557760) * (q : ℂ) ^ 6
      | 3 => -((1 : ℂ) / 9216) * (q : ℂ) ^ 3 - ((1 : ℂ) / 49152) * (q : ℂ) ^ 4
          - ((1 : ℂ) / 983040) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 737280) * (q : ℂ) ^ 4
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 5 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 9) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => ((427 : ℂ) / 62914560) - ((5233 : ℂ) / 13589544960) * (q : ℂ)
            - ((12533 : ℂ) / 108716359680) * (q : ℂ) ^ 2 - ((7789 : ℂ) / 579820584960) * (q : ℂ) ^ 3
            + ((18007 : ℂ) / 41747082117120) * (q : ℂ) ^ 4
            + ((475201 : ℂ) / 1335906627747840) * (q : ℂ) ^ 5
            + ((913 : ℂ) / 33397665693696) * (q : ℂ) ^ 6
            - ((6889 : ℂ) / 1252412463513600) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((131 : ℂ) / 15728640) - ((1333 : ℂ) / 339738624) * (q : ℂ)
            - ((5587 : ℂ) / 27179089920) * (q : ℂ) ^ 2 + ((419 : ℂ) / 72477573120) * (q : ℂ) ^ 3
            + ((25013 : ℂ) / 5218385264640) * (q : ℂ) ^ 4
            + ((103723 : ℂ) / 166988328468480) * (q : ℂ) ^ 5
            - ((16231 : ℂ) / 1335906627747840) * (q : ℂ) ^ 6
            - ((59677 : ℂ) / 5009649854054400) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((31 : ℂ) / 1474560) - ((11 : ℂ) / 1966080) * (q : ℂ)
            + ((11 : ℂ) / 3397386240) * (q : ℂ) ^ 2 + ((49 : ℂ) / 3397386240) * (q : ℂ) ^ 3
            + ((571 : ℂ) / 217432719360) * (q : ℂ) ^ 4 - ((1073 : ℂ) / 20873541058560) * (q : ℂ) ^ 5
            - ((1163 : ℂ) / 27831388078080) * (q : ℂ) ^ 6 - ((83 : ℂ) / 34789235097600) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 46080) - ((1 : ℂ) / 1179648) * (q : ℂ)
            + ((1 : ℂ) / 47185920) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1132462080) * (q : ℂ) ^ 3
            - ((11 : ℂ) / 27179089920) * (q : ℂ) ^ 4 - ((49 : ℂ) / 434865438720) * (q : ℂ) ^ 5
            - ((11 : ℂ) / 1391569403904) * (q : ℂ) ^ 6 + ((83 : ℂ) / 26091926323200) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 737280))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.3**: `b₁(q) = 1 - q - q²/8 + q³/64 - q⁴/1536 - 11q⁵/36864 + 49q⁶/589824
- 55q⁷/9437184 - 83q⁸/35389440 + O(q⁹)`. -/
@[dlmf 28.6.E3]
theorem mathieuB_one_small_q :
    (fun q : ℝ => mathieuB 1 q - (1 - q - 1 / 8 * q ^ 2 + 1 / 64 * q ^ 3 - 1 / 1536 * q ^ 4 -
      11 / 36864 * q ^ 5 + 49 / 589824 * q ^ 6 - 55 / 9437184 * q ^ 7 -
      83 / 35389440 * q ^ 8)) =O[𝓝 0] (fun q => q ^ 9) := by
  refine p3q_real_of_complex (p3q_eig_BO 0 (N := 9) (K := 9)
    (p := fun q : ℝ => (1 : ℂ) - (1 : ℂ) * (q : ℂ) - ((1 : ℂ) / 8) * (q : ℂ) ^ 2
      + ((1 : ℂ) / 64) * (q : ℂ) ^ 3 - ((1 : ℂ) / 1536) * (q : ℂ) ^ 4
      - ((11 : ℂ) / 36864) * (q : ℂ) ^ 5 + ((49 : ℂ) / 589824) * (q : ℂ) ^ 6
      - ((55 : ℂ) / 9437184) * (q : ℂ) ^ 7 - ((83 : ℂ) / 35389440) * (q : ℂ) ^ 8)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 8) * (q : ℂ) + ((1 : ℂ) / 64) * (q : ℂ) ^ 2
          - ((1 : ℂ) / 1536) * (q : ℂ) ^ 3 - ((11 : ℂ) / 36864) * (q : ℂ) ^ 4
          + ((49 : ℂ) / 589824) * (q : ℂ) ^ 5 - ((55 : ℂ) / 9437184) * (q : ℂ) ^ 6
          - ((83 : ℂ) / 35389440) * (q : ℂ) ^ 7
      | 2 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2 - ((1 : ℂ) / 1152) * (q : ℂ) ^ 3
          + ((1 : ℂ) / 24576) * (q : ℂ) ^ 4 + ((7 : ℂ) / 393216) * (q : ℂ) ^ 5
          - ((719 : ℂ) / 141557760) * (q : ℂ) ^ 6
      | 3 => -((1 : ℂ) / 9216) * (q : ℂ) ^ 3 + ((1 : ℂ) / 49152) * (q : ℂ) ^ 4
          - ((1 : ℂ) / 983040) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 737280) * (q : ℂ) ^ 4
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 5 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 9) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => -((427 : ℂ) / 62914560) - ((5233 : ℂ) / 13589544960) * (q : ℂ)
            + ((12533 : ℂ) / 108716359680) * (q : ℂ) ^ 2 - ((7789 : ℂ) / 579820584960) * (q : ℂ) ^ 3
            - ((18007 : ℂ) / 41747082117120) * (q : ℂ) ^ 4
            + ((475201 : ℂ) / 1335906627747840) * (q : ℂ) ^ 5
            - ((913 : ℂ) / 33397665693696) * (q : ℂ) ^ 6
            - ((6889 : ℂ) / 1252412463513600) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((131 : ℂ) / 15728640) - ((1333 : ℂ) / 339738624) * (q : ℂ)
            + ((5587 : ℂ) / 27179089920) * (q : ℂ) ^ 2 + ((419 : ℂ) / 72477573120) * (q : ℂ) ^ 3
            - ((25013 : ℂ) / 5218385264640) * (q : ℂ) ^ 4
            + ((103723 : ℂ) / 166988328468480) * (q : ℂ) ^ 5
            + ((16231 : ℂ) / 1335906627747840) * (q : ℂ) ^ 6
            - ((59677 : ℂ) / 5009649854054400) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => ((31 : ℂ) / 1474560) - ((11 : ℂ) / 1966080) * (q : ℂ)
            - ((11 : ℂ) / 3397386240) * (q : ℂ) ^ 2 + ((49 : ℂ) / 3397386240) * (q : ℂ) ^ 3
            - ((571 : ℂ) / 217432719360) * (q : ℂ) ^ 4 - ((1073 : ℂ) / 20873541058560) * (q : ℂ) ^ 5
            + ((1163 : ℂ) / 27831388078080) * (q : ℂ) ^ 6 - ((83 : ℂ) / 34789235097600) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 46080) - ((1 : ℂ) / 1179648) * (q : ℂ)
            - ((1 : ℂ) / 47185920) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1132462080) * (q : ℂ) ^ 3
            + ((11 : ℂ) / 27179089920) * (q : ℂ) ^ 4 - ((49 : ℂ) / 434865438720) * (q : ℂ) ^ 5
            + ((11 : ℂ) / 1391569403904) * (q : ℂ) ^ 6 + ((83 : ℂ) / 26091926323200) * (q : ℂ) ^ 7)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 737280))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.4**: `a₂(q) = 4 + 5q²/12 - 763q⁴/13824 + 1002401q⁶/79626240
- 1669068401q⁸/458647142400 + O(q¹⁰)`. -/
@[dlmf 28.6.E4]
theorem mathieuA_two_small_q :
    (fun q : ℝ => mathieuA 2 q - (4 + 5 / 12 * q ^ 2 - 763 / 13824 * q ^ 4 +
      1002401 / 79626240 * q ^ 6 - 1669068401 / 458647142400 * q ^ 8)) =O[𝓝 0]
      (fun q => q ^ 10) := by
  refine p3q_real_of_complex (p3q_eig_AE 1 (N := 11) (K := 10)
    (p := fun q : ℝ => (4 : ℂ) + ((5 : ℂ) / 12) * (q : ℂ) ^ 2 - ((763 : ℂ) / 13824) * (q : ℂ) ^ 4
      + ((1002401 : ℂ) / 79626240) * (q : ℂ) ^ 6 - ((1669068401 : ℂ) / 458647142400) * (q : ℂ) ^ 8)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 4) * (q : ℂ) - ((5 : ℂ) / 192) * (q : ℂ) ^ 3
          + ((1363 : ℂ) / 221184) * (q : ℂ) ^ 5 - ((2278001 : ℂ) / 1274019840) * (q : ℂ) ^ 7
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 12) * (q : ℂ) - ((43 : ℂ) / 13824) * (q : ℂ) ^ 3
          + ((21041 : ℂ) / 79626240) * (q : ℂ) ^ 5 - ((28907681 : ℂ) / 458647142400) * (q : ℂ) ^ 7
      | 3 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2 + ((293 : ℂ) / 2211840) * (q : ℂ) ^ 4
          - ((139453 : ℂ) / 12740198400) * (q : ℂ) ^ 6
      | 4 => -((1 : ℂ) / 23040) * (q : ℂ) ^ 3 - ((167 : ℂ) / 66355200) * (q : ℂ) ^ 5
      | 5 => ((1 : ℂ) / 2211840) * (q : ℂ) ^ 4
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | 10 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 6 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 9) (by decide)
          (s := fun q : ℝ => ((4261291001 : ℂ) / 1834588569600)
            - ((1591151909 : ℂ) / 5870683422720) * (q : ℂ) ^ 2
            + ((14069168861 : ℂ) / 313103115878400) * (q : ℂ) ^ 4
            - ((3802139486546401 : ℂ) / 584325558976905216000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 10) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 9) (by decide)
          (s := fun q : ℝ => -((614371183 : ℂ) / 2751882854400)
            - ((114918021287 : ℂ) / 6340338096537600) * (q : ℂ) ^ 2
            + ((32047978283761 : ℂ) / 18260173718028288000) * (q : ℂ) ^ 4
            - ((48248896903288081 : ℂ) / 210357201231685877760000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => -((9624629 : ℂ) / 114661785600)
            + ((422987423 : ℂ) / 58706834227200) * (q : ℂ) ^ 2
            + ((34934714897 : ℂ) / 56358560858112000) * (q : ℂ) ^ 4
            - ((232756595724653 : ℂ) / 5843255589769052160000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((156613 : ℂ) / 12740198400)
            + ((747559 : ℂ) / 1834588569600) * (q : ℂ) ^ 2
            - ((444755489 : ℂ) / 3522410053632000) * (q : ℂ) ^ 4
            - ((278734422967 : ℂ) / 30433622863380480000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((359 : ℂ) / 132710400) + ((763 : ℂ) / 30576476160) * (q : ℂ) ^ 2
            - ((1002401 : ℂ) / 176120502681600) * (q : ℂ) ^ 4
            + ((1669068401 : ℂ) / 1014454095446016000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 2211840))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.5**: `b₂(q) = 4 - q²/12 + 5q⁴/13824 - 289q⁶/79626240
+ 21391q⁸/458647142400 + O(q¹⁰)`. -/
@[dlmf 28.6.E5]
theorem mathieuB_two_small_q :
    (fun q : ℝ => mathieuB 2 q - (4 - 1 / 12 * q ^ 2 + 5 / 13824 * q ^ 4 -
      289 / 79626240 * q ^ 6 + 21391 / 458647142400 * q ^ 8)) =O[𝓝 0]
      (fun q => q ^ 10) := by
  refine p3q_real_of_complex (p3q_eig_BE 0 (N := 10) (K := 10)
    (p := fun q : ℝ => (4 : ℂ) - ((1 : ℂ) / 12) * (q : ℂ) ^ 2 + ((5 : ℂ) / 13824) * (q : ℂ) ^ 4
      - ((289 : ℂ) / 79626240) * (q : ℂ) ^ 6 + ((21391 : ℂ) / 458647142400) * (q : ℂ) ^ 8)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => (1 : ℂ)
      | 1 => -((1 : ℂ) / 12) * (q : ℂ) + ((5 : ℂ) / 13824) * (q : ℂ) ^ 3
          - ((289 : ℂ) / 79626240) * (q : ℂ) ^ 5 + ((21391 : ℂ) / 458647142400) * (q : ℂ) ^ 7
      | 2 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2 - ((37 : ℂ) / 2211840) * (q : ℂ) ^ 4
          + ((2243 : ℂ) / 12740198400) * (q : ℂ) ^ 6
      | 3 => -((1 : ℂ) / 23040) * (q : ℂ) ^ 3 + ((11 : ℂ) / 33177600) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 2211840) * (q : ℂ) ^ 4
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 5 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 10) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 9) (by decide)
          (s := fun q : ℝ => ((3577 : ℂ) / 343985356800)
            - ((297431 : ℂ) / 6340338096537600) * (q : ℂ) ^ 2
            + ((6181999 : ℂ) / 18260173718028288000) * (q : ℂ) ^ 4
            - ((457574881 : ℂ) / 210357201231685877760000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => ((3523 : ℂ) / 45864714240) - ((4811 : ℂ) / 19568944742400) * (q : ℂ) ^ 2
            + ((8887 : ℂ) / 6262062317568000) * (q : ℂ) ^ 4
            - ((47980013 : ℂ) / 5843255589769052160000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((559 : ℂ) / 2548039680) - ((509 : ℂ) / 1834588569600) * (q : ℂ) ^ 2
            + ((11369 : ℂ) / 3522410053632000) * (q : ℂ) ^ 4
            - ((235301 : ℂ) / 15216811431690240000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => ((49 : ℂ) / 132710400) - ((1 : ℂ) / 6115295232) * (q : ℂ) ^ 2
            + ((289 : ℂ) / 176120502681600) * (q : ℂ) ^ 4
            - ((21391 : ℂ) / 1014454095446016000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 2211840))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.6**: `a₃(q) = 9 + q²/16 + q³/64 + 13q⁴/20480 - 5q⁵/16384 - 1961q⁶/23592960
- 609q⁷/104857600 + O(q⁸)`. -/
@[dlmf 28.6.E6]
theorem mathieuA_three_small_q :
    (fun q : ℝ => mathieuA 3 q - (9 + 1 / 16 * q ^ 2 + 1 / 64 * q ^ 3 + 13 / 20480 * q ^ 4 -
      5 / 16384 * q ^ 5 - 1961 / 23592960 * q ^ 6 - 609 / 104857600 * q ^ 7)) =O[𝓝 0]
      (fun q => q ^ 8) := by
  refine p3q_real_of_complex (p3q_eig_AO 1 (N := 9) (K := 8)
    (p := fun q : ℝ => (9 : ℂ) + ((1 : ℂ) / 16) * (q : ℂ) ^ 2 + ((1 : ℂ) / 64) * (q : ℂ) ^ 3
      + ((13 : ℂ) / 20480) * (q : ℂ) ^ 4 - ((5 : ℂ) / 16384) * (q : ℂ) ^ 5
      - ((1961 : ℂ) / 23592960) * (q : ℂ) ^ 6 - ((609 : ℂ) / 104857600) * (q : ℂ) ^ 7)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 8) * (q : ℂ) + ((1 : ℂ) / 64) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1024) * (q : ℂ) ^ 3
          - ((1 : ℂ) / 4096) * (q : ℂ) ^ 4 - ((103 : ℂ) / 1310720) * (q : ℂ) ^ 5
          - ((33 : ℂ) / 5242880) * (q : ℂ) ^ 6
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 16) * (q : ℂ) - ((7 : ℂ) / 20480) * (q : ℂ) ^ 3
          - ((1 : ℂ) / 16384) * (q : ℂ) ^ 4 - ((107 : ℂ) / 23592960) * (q : ℂ) ^ 5
          + ((51 : ℂ) / 104857600) * (q : ℂ) ^ 6
      | 3 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2 + ((17 : ℂ) / 1474560) * (q : ℂ) ^ 4
          + ((7 : ℂ) / 3276800) * (q : ℂ) ^ 5
      | 4 => -((1 : ℂ) / 46080) * (q : ℂ) ^ 3
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 5 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((3203 : ℂ) / 188743680) + ((15473 : ℂ) / 3774873600) * (q : ℂ)
            + ((11869 : ℂ) / 48318382080) * (q : ℂ) ^ 2 - ((33443 : ℂ) / 966367641600) * (q : ℂ) ^ 3
            - ((305231 : ℂ) / 30923764531200) * (q : ℂ) ^ 4
            - ((403891 : ℂ) / 412316860416000) * (q : ℂ) ^ 5
            - ((20097 : ℂ) / 549755813888000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((1569 : ℂ) / 419430400) - ((293 : ℂ) / 754974720) * (q : ℂ)
            - ((521 : ℂ) / 10066329600) * (q : ℂ) ^ 2 - ((28189 : ℂ) / 3221225472000) * (q : ℂ) ^ 3
            - ((324523 : ℂ) / 556627761561600) * (q : ℂ) ^ 4
            + ((121 : ℂ) / 8589934592000) * (q : ℂ) ^ 5
            + ((31059 : ℂ) / 10995116277760000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((737 : ℂ) / 117964800) + ((613 : ℂ) / 943718400) * (q : ℂ)
            + ((2693 : ℂ) / 30198988800) * (q : ℂ) ^ 2 + ((6787 : ℂ) / 603979776000) * (q : ℂ) ^ 3
            + ((56017 : ℂ) / 34789235097600) * (q : ℂ) ^ 4
            + ((37807 : ℂ) / 154618822656000) * (q : ℂ) ^ 5
            + ((4263 : ℂ) / 343597383680000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((19 : ℂ) / 1474560) + ((73 : ℂ) / 29491200) * (q : ℂ)
            + ((13 : ℂ) / 943718400) * (q : ℂ) ^ 2 - ((1 : ℂ) / 150994944) * (q : ℂ) ^ 3
            - ((1961 : ℂ) / 1087163596800) * (q : ℂ) ^ 4 - ((203 : ℂ) / 1610612736000) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 46080))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.7**: `b₃(q) = 9 + q²/16 - q³/64 + 13q⁴/20480 + 5q⁵/16384 - 1961q⁶/23592960
+ 609q⁷/104857600 + O(q⁸)`. -/
@[dlmf 28.6.E7]
theorem mathieuB_three_small_q :
    (fun q : ℝ => mathieuB 3 q - (9 + 1 / 16 * q ^ 2 - 1 / 64 * q ^ 3 + 13 / 20480 * q ^ 4 +
      5 / 16384 * q ^ 5 - 1961 / 23592960 * q ^ 6 + 609 / 104857600 * q ^ 7)) =O[𝓝 0]
      (fun q => q ^ 8) := by
  refine p3q_real_of_complex (p3q_eig_BO 1 (N := 9) (K := 8)
    (p := fun q : ℝ => (9 : ℂ) + ((1 : ℂ) / 16) * (q : ℂ) ^ 2 - ((1 : ℂ) / 64) * (q : ℂ) ^ 3
      + ((13 : ℂ) / 20480) * (q : ℂ) ^ 4 + ((5 : ℂ) / 16384) * (q : ℂ) ^ 5
      - ((1961 : ℂ) / 23592960) * (q : ℂ) ^ 6 + ((609 : ℂ) / 104857600) * (q : ℂ) ^ 7)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 8) * (q : ℂ) - ((1 : ℂ) / 64) * (q : ℂ) ^ 2 + ((1 : ℂ) / 1024) * (q : ℂ) ^ 3
          + ((1 : ℂ) / 4096) * (q : ℂ) ^ 4 - ((103 : ℂ) / 1310720) * (q : ℂ) ^ 5
          + ((33 : ℂ) / 5242880) * (q : ℂ) ^ 6
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 16) * (q : ℂ) - ((7 : ℂ) / 20480) * (q : ℂ) ^ 3
          + ((1 : ℂ) / 16384) * (q : ℂ) ^ 4 - ((107 : ℂ) / 23592960) * (q : ℂ) ^ 5
          - ((51 : ℂ) / 104857600) * (q : ℂ) ^ 6
      | 3 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2 + ((17 : ℂ) / 1474560) * (q : ℂ) ^ 4
          - ((7 : ℂ) / 3276800) * (q : ℂ) ^ 5
      | 4 => -((1 : ℂ) / 46080) * (q : ℂ) ^ 3
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 5 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((3203 : ℂ) / 188743680) - ((15473 : ℂ) / 3774873600) * (q : ℂ)
            + ((11869 : ℂ) / 48318382080) * (q : ℂ) ^ 2 + ((33443 : ℂ) / 966367641600) * (q : ℂ) ^ 3
            - ((305231 : ℂ) / 30923764531200) * (q : ℂ) ^ 4
            + ((403891 : ℂ) / 412316860416000) * (q : ℂ) ^ 5
            - ((20097 : ℂ) / 549755813888000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((1569 : ℂ) / 419430400) + ((293 : ℂ) / 754974720) * (q : ℂ)
            - ((521 : ℂ) / 10066329600) * (q : ℂ) ^ 2 + ((28189 : ℂ) / 3221225472000) * (q : ℂ) ^ 3
            - ((324523 : ℂ) / 556627761561600) * (q : ℂ) ^ 4
            - ((121 : ℂ) / 8589934592000) * (q : ℂ) ^ 5
            + ((31059 : ℂ) / 10995116277760000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((737 : ℂ) / 117964800) - ((613 : ℂ) / 943718400) * (q : ℂ)
            + ((2693 : ℂ) / 30198988800) * (q : ℂ) ^ 2 - ((6787 : ℂ) / 603979776000) * (q : ℂ) ^ 3
            + ((56017 : ℂ) / 34789235097600) * (q : ℂ) ^ 4
            - ((37807 : ℂ) / 154618822656000) * (q : ℂ) ^ 5
            + ((4263 : ℂ) / 343597383680000) * (q : ℂ) ^ 6)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((19 : ℂ) / 1474560) - ((73 : ℂ) / 29491200) * (q : ℂ)
            + ((13 : ℂ) / 943718400) * (q : ℂ) ^ 2 + ((1 : ℂ) / 150994944) * (q : ℂ) ^ 3
            - ((1961 : ℂ) / 1087163596800) * (q : ℂ) ^ 4 + ((203 : ℂ) / 1610612736000) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 46080))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.8**: `a₄(q) = 16 + q²/30 + 433q⁴/864000 - 5701q⁶/2721600000 + O(q⁸)`. -/
@[dlmf 28.6.E8]
theorem mathieuA_four_small_q :
    (fun q : ℝ => mathieuA 4 q - (16 + 1 / 30 * q ^ 2 + 433 / 864000 * q ^ 4 -
      5701 / 2721600000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  refine p3q_real_of_complex (p3q_eig_AE 2 (N := 10) (K := 8)
    (p := fun q : ℝ => (16 : ℂ) + ((1 : ℂ) / 30) * (q : ℂ) ^ 2 + ((433 : ℂ) / 864000) * (q : ℂ) ^ 4
      - ((5701 : ℂ) / 2721600000) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 192) * (q : ℂ) ^ 2 + ((1 : ℂ) / 34560) * (q : ℂ) ^ 4
      | 1 => ((1 : ℂ) / 12) * (q : ℂ) + ((11 : ℂ) / 17280) * (q : ℂ) ^ 3
          - ((53 : ℂ) / 124416000) * (q : ℂ) ^ 5
      | 2 => (1 : ℂ)
      | 3 => -((1 : ℂ) / 20) * (q : ℂ) - ((13 : ℂ) / 96000) * (q : ℂ) ^ 3
          - ((4037 : ℂ) / 2419200000) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2 + ((23 : ℂ) / 6048000) * (q : ℂ) ^ 4
      | 5 => -((1 : ℂ) / 80640) * (q : ℂ) ^ 3
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 6 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((1991 : ℂ) / 497664000) - ((139 : ℂ) / 38707200000) * (q : ℂ) ^ 2
            + ((5701 : ℂ) / 94058496000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((68069 : ℂ) / 522547200000)
            + ((1164019 : ℂ) / 752467968000000) * (q : ℂ) ^ 2
            - ((302153 : ℂ) / 338610585600000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((6533 : ℂ) / 348364800000)
            + ((385039 : ℂ) / 696729600000000) * (q : ℂ) ^ 2
            - ((23014937 : ℂ) / 6584094720000000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((67279 : ℂ) / 29030400000) + ((481 : ℂ) / 1741824000000) * (q : ℂ) ^ 2
            + ((131123 : ℂ) / 16460236800000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((17 : ℂ) / 4032000) + ((433 : ℂ) / 69672960000) * (q : ℂ) ^ 2
            - ((5701 : ℂ) / 219469824000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 80640))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.9**: `b₄(q) = 16 + q²/30 - 317q⁴/864000 + 10049q⁶/2721600000 + O(q⁸)`. -/
@[dlmf 28.6.E9]
theorem mathieuB_four_small_q :
    (fun q : ℝ => mathieuB 4 q - (16 + 1 / 30 * q ^ 2 - 317 / 864000 * q ^ 4 +
      10049 / 2721600000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  refine p3q_real_of_complex (p3q_eig_BE 1 (N := 9) (K := 8)
    (p := fun q : ℝ => (16 : ℂ) + ((1 : ℂ) / 30) * (q : ℂ) ^ 2 - ((317 : ℂ) / 864000) * (q : ℂ) ^ 4
      + ((10049 : ℂ) / 2721600000) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 12) * (q : ℂ) - ((1 : ℂ) / 4320) * (q : ℂ) ^ 3
          + ((397 : ℂ) / 124416000) * (q : ℂ) ^ 5
      | 1 => (1 : ℂ)
      | 2 => -((1 : ℂ) / 20) * (q : ℂ) - ((13 : ℂ) / 96000) * (q : ℂ) ^ 3
          + ((1213 : ℂ) / 2419200000) * (q : ℂ) ^ 5
      | 3 => ((1 : ℂ) / 960) * (q : ℂ) ^ 2 + ((23 : ℂ) / 6048000) * (q : ℂ) ^ 4
      | 4 => -((1 : ℂ) / 80640) * (q : ℂ) ^ 3
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 5 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((32593 : ℂ) / 65318400000)
            + ((1524079 : ℂ) / 752467968000000) * (q : ℂ) ^ 2
            - ((3989453 : ℂ) / 338610585600000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((41183 : ℂ) / 348364800000)
            + ((68077 : ℂ) / 99532800000000) * (q : ℂ) ^ 2
            - ((12189437 : ℂ) / 6584094720000000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => ((21971 : ℂ) / 29030400000) - ((1423 : ℂ) / 580608000000) * (q : ℂ) ^ 2
            - ((231127 : ℂ) / 16460236800000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((17 : ℂ) / 4032000) - ((317 : ℂ) / 69672960000) * (q : ℂ) ^ 2
            + ((10049 : ℂ) / 219469824000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 80640))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.10**: `a₅(q) = 25 + q²/48 + 11q⁴/774144 + q⁵/147456 + 37q⁶/891813888
+ O(q⁷)`. -/
@[dlmf 28.6.E10]
theorem mathieuA_five_small_q :
    (fun q : ℝ => mathieuA 5 q - (25 + 1 / 48 * q ^ 2 + 11 / 774144 * q ^ 4 +
      1 / 147456 * q ^ 5 + 37 / 891813888 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  refine p3q_real_of_complex (p3q_eig_AO 2 (N := 9) (K := 7)
    (p := fun q : ℝ => (25 : ℂ) + ((1 : ℂ) / 48) * (q : ℂ) ^ 2 + ((11 : ℂ) / 774144) * (q : ℂ) ^ 4
      + ((1 : ℂ) / 147456) * (q : ℂ) ^ 5 + ((37 : ℂ) / 891813888) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2 + ((1 : ℂ) / 9216) * (q : ℂ) ^ 3
          + ((5 : ℂ) / 884736) * (q : ℂ) ^ 4
      | 1 => ((1 : ℂ) / 16) * (q : ℂ) + ((1 : ℂ) / 12288) * (q : ℂ) ^ 3
          + ((1 : ℂ) / 147456) * (q : ℂ) ^ 4 + ((19 : ℂ) / 99090432) * (q : ℂ) ^ 5
      | 2 => (1 : ℂ)
      | 3 => -((1 : ℂ) / 24) * (q : ℂ) - ((13 : ℂ) / 193536) * (q : ℂ) ^ 3
          - ((67 : ℂ) / 445906944) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 1344) * (q : ℂ) ^ 2 + ((5 : ℂ) / 3096576) * (q : ℂ) ^ 4
      | 5 => -((1 : ℂ) / 129024) * (q : ℂ) ^ 3
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 6 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 98304) + ((11 : ℂ) / 297271296) * (q : ℂ)
            - ((137 : ℂ) / 7134511104) * (q : ℂ) ^ 2 - ((211 : ℂ) / 228304355328) * (q : ℂ) ^ 3
            - ((11 : ℂ) / 256842399744) * (q : ℂ) ^ 4 - ((185 : ℂ) / 789019852013568) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 1769472) - ((221 : ℂ) / 28538044416) * (q : ℂ)
            - ((37 : ℂ) / 57076088832) * (q : ℂ) ^ 2 - ((37 : ℂ) / 710280216576) * (q : ℂ) ^ 3
            - ((13 : ℂ) / 8218956791808) * (q : ℂ) ^ 4
            - ((703 : ℂ) / 88370223425519616) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 3538944) + ((871 : ℂ) / 149824733184) * (q : ℂ)
            + ((13 : ℂ) / 28538044416) * (q : ℂ) ^ 2 + ((1699 : ℂ) / 345196185255936) * (q : ℂ) ^ 3
            + ((67 : ℂ) / 65751654334464) * (q : ℂ) ^ 4
            + ((2479 : ℂ) / 397666005414838272) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((607 : ℂ) / 3121348608) - ((1 : ℂ) / 198180864) * (q : ℂ)
            - ((43 : ℂ) / 799065243648) * (q : ℂ) ^ 2 - ((5 : ℂ) / 456608710656) * (q : ℂ) ^ 3
            - ((185 : ℂ) / 2761569482047488) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((11 : ℂ) / 6193152) + ((11 : ℂ) / 99883155456) * (q : ℂ) ^ 2
            + ((1 : ℂ) / 19025362944) * (q : ℂ) ^ 3 + ((37 : ℂ) / 115065395085312) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 129024))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.11**: `b₅(q) = 25 + q²/48 + 11q⁴/774144 - q⁵/147456 + 37q⁶/891813888
+ O(q⁷)`. -/
@[dlmf 28.6.E11]
theorem mathieuB_five_small_q :
    (fun q : ℝ => mathieuB 5 q - (25 + 1 / 48 * q ^ 2 + 11 / 774144 * q ^ 4 -
      1 / 147456 * q ^ 5 + 37 / 891813888 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  refine p3q_real_of_complex (p3q_eig_BO 2 (N := 9) (K := 7)
    (p := fun q : ℝ => (25 : ℂ) + ((1 : ℂ) / 48) * (q : ℂ) ^ 2 + ((11 : ℂ) / 774144) * (q : ℂ) ^ 4
      - ((1 : ℂ) / 147456) * (q : ℂ) ^ 5 + ((37 : ℂ) / 891813888) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 384) * (q : ℂ) ^ 2 - ((1 : ℂ) / 9216) * (q : ℂ) ^ 3
          + ((5 : ℂ) / 884736) * (q : ℂ) ^ 4
      | 1 => ((1 : ℂ) / 16) * (q : ℂ) + ((1 : ℂ) / 12288) * (q : ℂ) ^ 3
          - ((1 : ℂ) / 147456) * (q : ℂ) ^ 4 + ((19 : ℂ) / 99090432) * (q : ℂ) ^ 5
      | 2 => (1 : ℂ)
      | 3 => -((1 : ℂ) / 24) * (q : ℂ) - ((13 : ℂ) / 193536) * (q : ℂ) ^ 3
          - ((67 : ℂ) / 445906944) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 1344) * (q : ℂ) ^ 2 + ((5 : ℂ) / 3096576) * (q : ℂ) ^ 4
      | 5 => -((1 : ℂ) / 129024) * (q : ℂ) ^ 3
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 6 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 98304) + ((11 : ℂ) / 297271296) * (q : ℂ)
            + ((137 : ℂ) / 7134511104) * (q : ℂ) ^ 2 - ((211 : ℂ) / 228304355328) * (q : ℂ) ^ 3
            + ((11 : ℂ) / 256842399744) * (q : ℂ) ^ 4 - ((185 : ℂ) / 789019852013568) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => ((1 : ℂ) / 1769472) - ((221 : ℂ) / 28538044416) * (q : ℂ)
            + ((37 : ℂ) / 57076088832) * (q : ℂ) ^ 2 - ((37 : ℂ) / 710280216576) * (q : ℂ) ^ 3
            + ((13 : ℂ) / 8218956791808) * (q : ℂ) ^ 4
            - ((703 : ℂ) / 88370223425519616) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 3538944) + ((871 : ℂ) / 149824733184) * (q : ℂ)
            - ((13 : ℂ) / 28538044416) * (q : ℂ) ^ 2 + ((1699 : ℂ) / 345196185255936) * (q : ℂ) ^ 3
            - ((67 : ℂ) / 65751654334464) * (q : ℂ) ^ 4
            + ((2479 : ℂ) / 397666005414838272) * (q : ℂ) ^ 5)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((607 : ℂ) / 3121348608) + ((1 : ℂ) / 198180864) * (q : ℂ)
            - ((43 : ℂ) / 799065243648) * (q : ℂ) ^ 2 + ((5 : ℂ) / 456608710656) * (q : ℂ) ^ 3
            - ((185 : ℂ) / 2761569482047488) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((11 : ℂ) / 6193152) + ((11 : ℂ) / 99883155456) * (q : ℂ) ^ 2
            - ((1 : ℂ) / 19025362944) * (q : ℂ) ^ 3 + ((37 : ℂ) / 115065395085312) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 129024))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.12**: `a₆(q) = 36 + q²/70 + 187q⁴/43904000
+ 6743617q⁶/92935987200000 + O(q⁸)`. -/
@[dlmf 28.6.E12]
theorem mathieuA_six_small_q :
    (fun q : ℝ => mathieuA 6 q - (36 + 1 / 70 * q ^ 2 + 187 / 43904000 * q ^ 4 +
      6743617 / 92935987200000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  refine p3q_real_of_complex (p3q_eig_AE 3 (N := 11) (K := 8)
    (p := fun q : ℝ => (36 : ℂ) + ((1 : ℂ) / 70) * (q : ℂ) ^ 2
      + ((187 : ℂ) / 43904000) * (q : ℂ) ^ 4 + ((6743617 : ℂ) / 92935987200000) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 23040) * (q : ℂ) ^ 3
      | 1 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2 + ((431 : ℂ) / 129024000) * (q : ℂ) ^ 4
      | 2 => ((1 : ℂ) / 20) * (q : ℂ) + ((19 : ℂ) / 448000) * (q : ℂ) ^ 3
          + ((79711 : ℂ) / 632217600000) * (q : ℂ) ^ 5
      | 3 => (1 : ℂ)
      | 4 => -((1 : ℂ) / 28) * (q : ℂ) - ((67 : ℂ) / 1756160) * (q : ℂ) ^ 3
          - ((49739 : ℂ) / 929359872000) * (q : ℂ) ^ 5
      | 5 => ((1 : ℂ) / 1792) * (q : ℂ) ^ 2 + ((19 : ℂ) / 23708160) * (q : ℂ) ^ 4
      | 6 => -((1 : ℂ) / 193536) * (q : ℂ) ^ 3
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | 10 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 7 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((39 : ℂ) / 14336000) - ((187 : ℂ) / 1011548160000) * (q : ℂ) ^ 2
            - ((6743617 : ℂ) / 2141245145088000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => ((90667 : ℂ) / 1264435200000)
            - ((15179771 : ℂ) / 118958063616000000) * (q : ℂ) ^ 2
            - ((2906498927 : ℂ) / 11990972812492800000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((834179 : ℂ) / 148697579520000)
            - ((300975317 : ℂ) / 83270644531200000000) * (q : ℂ) ^ 2
            - ((537540454687 : ℂ) / 58755766781214720000000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((1356449 : ℂ) / 385512243200000)
            + ((163009037 : ℂ) / 54403487760384000000) * (q : ℂ) ^ 2
            + ((335420765963 : ℂ) / 86370977168385638400000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((1001407 : ℂ) / 14869757952000)
            - ((7312097 : ℂ) / 166541289062400000) * (q : ℂ) ^ 2
            - ((128128723 : ℂ) / 2203341254295552000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((83 : ℂ) / 94832640) + ((187 : ℂ) / 8497004544000) * (q : ℂ) ^ 2
            + ((6743617 : ℂ) / 17986459218739200000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 193536))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.13**: `b₆(q) = 36 + q²/70 + 187q⁴/43904000
- 5861633q⁶/92935987200000 + O(q⁸)`. -/
@[dlmf 28.6.E13]
theorem mathieuB_six_small_q :
    (fun q : ℝ => mathieuB 6 q - (36 + 1 / 70 * q ^ 2 + 187 / 43904000 * q ^ 4 -
      5861633 / 92935987200000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  refine p3q_real_of_complex (p3q_eig_BE 2 (N := 10) (K := 8)
    (p := fun q : ℝ => (36 : ℂ) + ((1 : ℂ) / 70) * (q : ℂ) ^ 2
      + ((187 : ℂ) / 43904000) * (q : ℂ) ^ 4 - ((5861633 : ℂ) / 92935987200000) * (q : ℂ) ^ 6)
    (v := fun (q : ℝ) (i : ℕ) => match i with
      | 0 => ((1 : ℂ) / 640) * (q : ℂ) ^ 2 + ((9 : ℂ) / 14336000) * (q : ℂ) ^ 4
      | 1 => ((1 : ℂ) / 20) * (q : ℂ) + ((19 : ℂ) / 448000) * (q : ℂ) ^ 3
          - ((671 : ℂ) / 70246400000) * (q : ℂ) ^ 5
      | 2 => (1 : ℂ)
      | 3 => -((1 : ℂ) / 28) * (q : ℂ) - ((67 : ℂ) / 1756160) * (q : ℂ) ^ 3
          - ((49739 : ℂ) / 929359872000) * (q : ℂ) ^ 5
      | 4 => ((1 : ℂ) / 1792) * (q : ℂ) ^ 2 + ((19 : ℂ) / 23708160) * (q : ℂ) ^ 4
      | 5 => -((1 : ℂ) / 193536) * (q : ℂ) ^ 3
      | 6 => 0
      | 7 => 0
      | 8 => 0
      | 9 => 0
      | _ => 0)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_) ?_
  · intro i hi
    interval_cases i <;> exact p3q_cont_isBigO_one (by fun_prop)
  · intro i hi
    by_cases htail : 6 < i
    · refine isBigO_residual_of_support htail ?_
      intro q j hj
      split <;> first | rfl | omega
    · interval_cases i
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((3537 : ℂ) / 140492800000)
            + ((11405179 : ℂ) / 118958063616000000) * (q : ℂ) ^ 2
            + ((5861633 : ℂ) / 148036701388800000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => ((462361 : ℂ) / 148697579520000)
            + ((226129933 : ℂ) / 83270644531200000000) * (q : ℂ) ^ 2
            - ((3933155743 : ℂ) / 6528418531246080000000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 8) (by decide)
          (s := fun q : ℝ => 0)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 7) (by decide)
          (s := fun q : ℝ => -((4598959 : ℂ) / 3469610188800000)
            - ((118508213 : ℂ) / 54403487760384000000) * (q : ℂ) ^ 2
            - ((291551763787 : ℂ) / 86370977168385638400000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 6) (by decide)
          (s := fun q : ℝ => -((1001407 : ℂ) / 14869757952000)
            + ((5293153 : ℂ) / 166541289062400000) * (q : ℂ) ^ 2
            + ((111371027 : ℂ) / 2203341254295552000000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 5) (by decide)
          (s := fun q : ℝ => ((83 : ℂ) / 94832640) + ((187 : ℂ) / 8497004544000) * (q : ℂ) ^ 2
            - ((5861633 : ℂ) / 17986459218739200000) * (q : ℂ) ^ 4)
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
      · exact p3q_isBigO_of_eq (e := 4) (by decide)
          (s := fun q : ℝ => -((1 : ℂ) / 193536))
          (fun q => by simp only [p3qL, p3qLo, Nat.reduceAdd]; push_cast; ring)
          (by fun_prop)
  · intro q; push_cast; ring_nf

/-- **DLMF 28.6.14** (`a_m`), `m ≥ 7`: `a_m(q) = m² + q²/(2(m²-1)) + (5m²+7)q⁴/(32(m²-1)³(m²-4))
+ (9m⁴+58m²+29)q⁶/(64(m²-1)⁵(m²-4)(m²-9)) + O(q^{min(m,8)})`. -/
@[dlmf 28.6.E14]
theorem mathieuA_small_q {m : ℕ} (hm : 7 ≤ m) :
    (fun q : ℝ => mathieuA m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ min m 8) := by
  rcases eq_or_lt_of_le hm with rfl | h8
  · refine p3q_mathieuA_seven.congr_left fun q => ?_
    norm_num
    ring
  · rw [min_eq_right (by omega)]
    exact p3q_mathieuA_ge8 h8

/-- **DLMF 28.6.14** (`b_m`), `m ≥ 7`: the same expansion for `b_m(q)`. -/
@[dlmf 28.6.E14]
theorem mathieuB_small_q {m : ℕ} (hm : 7 ≤ m) :
    (fun q : ℝ => mathieuB m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ min m 8) := by
  rcases eq_or_lt_of_le hm with rfl | h8
  · refine p3q_mathieuB_seven.congr_left fun q => ?_
    norm_num
    ring
  · rw [min_eq_right (by omega)]
    exact p3q_mathieuB_ge8 h8

/-- **DLMF 28.6.15**: `a_m(q) - b_m(q) = 2q^m/(2^{m-1}(m-1)!)² (1 + O(q²))`, `m ≥ 1`.
In particular (§28.6(i)) the power series of `a_m` and `b_m` agree up to the terms in `q^{m-1}`
(for `m = 2n` up to `q^{2n-2}`, for `m = 2n+1` up to `q^{2n}`). -/
@[dlmf 28.6.E15]
theorem mathieuA_sub_mathieuB_small_q {m : ℕ} (hm : 1 ≤ m) :
    ∃ ε : ℝ → ℝ, ε =O[𝓝 0] (fun q => q ^ 2) ∧ ∀ q : ℝ,
      mathieuA m q - mathieuB m q =
        2 * q ^ m / (2 ^ (m - 1) * ((m - 1).factorial : ℝ)) ^ 2 * (1 + ε q) := by
  sorry

/-- **DLMF 28.6.16** (`n ≥ 1`): for `a = a_{2n}(q)`,
`a - (2n)² - q²/(a - (2n-2)² - ⋯ q²/(a - 2² - 2q²/a)) = -q²/((2n+2)² - a - q²/((2n+4)² - a - ⋯))`;
the right side is the limit of the truncations `mathieuCFTail`. The left-side partial
denominators are assumed nonzero. -/
@[dlmf 28.6.E16]
theorem mathieuA_even_contFrac {n : ℕ} (hn : 1 ≤ n) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuA (2 * n) q) (mathieuA (2 * n) q)
      (fun k => if k = 0 then 2 else 1) (fun k => (2 * k + 2) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuA (2 * n) q) (fun k => (2 * n + 2 * k + 2) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuA (2 * n) q) (mathieuA (2 * n) q)
        (fun k => if k = 0 then 2 else 1) (fun k => (2 * k + 2) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.16, case `n = 0`**: `a₀(q) = -2q²/(4 - a₀ - q²/(16 - a₀ - ⋯))` (the printed
pattern degenerates at `n = 0`; the factor 2 comes from 28.4.5). -/
@[dlmf 28.6.E16]
theorem mathieuA_zero_contFrac (q : ℝ) :
    Tendsto (fun N => -2 * mathieuCFTail q (mathieuA 0 q) (fun k => (2 * k + 2) ^ 2) N)
      atTop (𝓝 (mathieuA 0 q : ℂ)) := by
  sorry

/-- **DLMF 28.6.17**: for `a = a_{2n+1}(q)`,
`a - (2n+1)² - q²/(a - (2n-1)² - ⋯ q²/(a - 3² - q²/(a - 1² - q)))
= -q²/((2n+3)² - a - q²/((2n+5)² - a - ⋯))`. -/
@[dlmf 28.6.E17]
theorem mathieuA_odd_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuA (2 * n + 1) q) (mathieuA (2 * n + 1) q - 1 - q)
      (fun _ => 1) (fun k => (2 * k + 3) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuA (2 * n + 1) q)
        (fun k => (2 * n + 2 * k + 3) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuA (2 * n + 1) q) (mathieuA (2 * n + 1) q - 1 - q)
        (fun _ => 1) (fun k => (2 * k + 3) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.18**: for `a = b_{2n+1}(q)`,
`a - (2n+1)² - q²/(a - (2n-1)² - ⋯ q²/(a - 3² - q²/(a - 1² + q)))
= -q²/((2n+3)² - a - q²/((2n+5)² - a - ⋯))`. -/
@[dlmf 28.6.E18]
theorem mathieuB_odd_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuB (2 * n + 1) q) (mathieuB (2 * n + 1) q - 1 + q)
      (fun _ => 1) (fun k => (2 * k + 3) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuB (2 * n + 1) q)
        (fun k => (2 * n + 2 * k + 3) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuB (2 * n + 1) q) (mathieuB (2 * n + 1) q - 1 + q)
        (fun _ => 1) (fun k => (2 * k + 3) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.19**: for `a = b_{2n+2}(q)`,
`a - (2n+2)² - q²/(a - (2n)² - ⋯ q²/(a - 2²)) = -q²/((2n+4)² - a - q²/((2n+6)² - a - ⋯))`. -/
@[dlmf 28.6.E19]
theorem mathieuB_even_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuB (2 * n + 2) q) (mathieuB (2 * n + 2) q - 4)
      (fun _ => 1) (fun k => (2 * k + 4) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuB (2 * n + 2) q)
        (fun k => (2 * n + 2 * k + 4) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuB (2 * n + 2) q) (mathieuB (2 * n + 2) q - 4)
        (fun _ => 1) (fun k => (2 * k + 4) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.20**: the radii of convergence `ρ_n^{(j)}` of the power series of `a_{2n}`
(`j = 1`), `b_{2n+2}` (`j = 2`), `a_{2n+1}` and `b_{2n+1}` (`j = 3`) satisfy
`liminf ρ_n^{(j)}/n² ≥ k k' K(k)²`, where `k ∈ (0, 1)` is the root of `2E(k) = K(k)` and
`k' = √(1 - k²)`. Stated as: for every `c < k k' K(k)²`, for all large `n` each of these
eigenvalues extends analytically from the real interval `(-cn², cn²)` to the disc `|q| < cn²`. -/
@[dlmf 28.6.E20]
theorem mathieu_radius_liminf {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1)
    (hEK : 2 * DLMF.EllipticIntegrals.compEllIntEk k = DLMF.JacobiElliptic.compEllIntKk k)
    {c : ℝ} (hc : c < k * Real.sqrt (1 - k ^ 2) * (DLMF.JacobiElliptic.compEllIntKk k).re ^ 2) :
    ∀ᶠ n : ℕ in atTop, ∀ e : ℕ → ℝ → ℝ, e ∈ ({fun n => mathieuA (2 * n),
        fun n => mathieuB (2 * n + 2), fun n => mathieuA (2 * n + 1),
        fun n => mathieuB (2 * n + 1)} : Set (ℕ → ℝ → ℝ)) →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 (c * n ^ 2)) ∧
        ∀ q : ℝ, |q| < c * n ^ 2 → F q = e n q := by
  sorry

/-! ### Functions `ce_n`, `se_n` (§28.6(ii)) -/

/-- **DLMF 28.6.21**: `2^{1/2} ce₀(z, q) = 1 - (q/2) cos 2z + (q²/32)(cos 4z - 2)
- (q³/128)((1/9) cos 6z - 11 cos 2z) + O(q⁴)`. -/
@[dlmf 28.6.E21]
theorem mathieuCe_zero_small_q (z : ℂ) :
    (fun q : ℝ => (Real.sqrt 2 : ℂ) * mathieuCe 0 z q - (1 - q / 2 * Complex.cos (2 * z) +
      q ^ 2 / 32 * (Complex.cos (4 * z) - 2) -
      q ^ 3 / 128 * (1 / 9 * Complex.cos (6 * z) - 11 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 4) :=
  p3q_ce0 z

/-- **DLMF 28.6.22**: `ce₁(z, q) = cos z - (q/8) cos 3z + (q²/128)((2/3) cos 5z - 2 cos 3z - cos z)
- (q³/1024)((1/9) cos 7z - (8/9) cos 5z - (1/3) cos 3z + 2 cos z) + O(q⁴)`. -/
@[dlmf 28.6.E22]
theorem mathieuCe_one_small_q (z : ℂ) :
    (fun q : ℝ => mathieuCe 1 z q - (Complex.cos z - q / 8 * Complex.cos (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.cos (5 * z) - 2 * Complex.cos (3 * z) - Complex.cos z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.cos (7 * z) - 8 / 9 * Complex.cos (5 * z) -
        1 / 3 * Complex.cos (3 * z) + 2 * Complex.cos z))) =O[𝓝 0] (fun q => q ^ 4) :=
  p3q_ce1 z

/-- **DLMF 28.6.23**: `se₁(z, q) = sin z - (q/8) sin 3z + (q²/128)((2/3) sin 5z + 2 sin 3z - sin z)
- (q³/1024)((1/9) sin 7z + (8/9) sin 5z - (1/3) sin 3z - 2 sin z) + O(q⁴)`. -/
@[dlmf 28.6.E23]
theorem mathieuSe_one_small_q (z : ℂ) :
    (fun q : ℝ => mathieuSe 1 z q - (Complex.sin z - q / 8 * Complex.sin (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.sin (5 * z) + 2 * Complex.sin (3 * z) - Complex.sin z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.sin (7 * z) + 8 / 9 * Complex.sin (5 * z) -
        1 / 3 * Complex.sin (3 * z) - 2 * Complex.sin z))) =O[𝓝 0] (fun q => q ^ 4) :=
  p3q_se1 z

/-- **DLMF 28.6.24**: `ce₂(z, q) = cos 2z - (q/4)((1/3) cos 4z - 1)
+ (q²/128)((1/3) cos 6z - (76/9) cos 2z) + O(q³)`. -/
@[dlmf 28.6.E24]
theorem mathieuCe_two_small_q (z : ℂ) :
    (fun q : ℝ => mathieuCe 2 z q - (Complex.cos (2 * z) -
      q / 4 * (1 / 3 * Complex.cos (4 * z) - 1) +
      q ^ 2 / 128 * (1 / 3 * Complex.cos (6 * z) - 76 / 9 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 3) :=
  p3q_ce2 z

/-- **DLMF 28.6.25**: `se₂(z, q) = sin 2z - (q/12) sin 4z + (q²/128)((1/3) sin 6z - (4/9) sin 2z)
+ O(q³)`. -/
@[dlmf 28.6.E25]
theorem mathieuSe_two_small_q (z : ℂ) :
    (fun q : ℝ => mathieuSe 2 z q - (Complex.sin (2 * z) - q / 12 * Complex.sin (4 * z) +
      q ^ 2 / 128 * (1 / 3 * Complex.sin (6 * z) - 4 / 9 * Complex.sin (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 3) :=
  p3q_se2 z

/-- **DLMF 28.6.26**: for `m ≥ 3`, `ce_m(z, q) = cos mz - (q/4)(cos(m+2)z/(m+1) - cos(m-2)z/(m-1))
+ (q²/32)(cos(m+4)z/((m+1)(m+2)) + cos(m-4)z/((m-1)(m-2)) - 2(m²+1) cos mz/(m²-1)²) + O(q³)`. -/
@[dlmf 28.6.E26]
theorem mathieuCe_small_q {m : ℕ} (hm : 3 ≤ m) (z : ℂ) :
    (fun q : ℝ => mathieuCe m z q - (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  rcases (show m = 3 ∨ m = 4 ∨ m = 5 ∨ 6 ≤ m by omega) with h | h | h | h
  · exact p3q_ce3 h z
  · exact p3q_ce4 h z
  · exact p3q_ce5 h z
  · exact p3q_ce_ge6 h z

/-- **DLMF §28.6(ii)**: for `m ≥ 3` the expansion of `se_m(z, q)` is 28.6.26 with `cos` replaced
by `sin` everywhere. -/
@[dlmf 28.6.ii]
theorem mathieuSe_small_q {m : ℕ} (hm : 3 ≤ m) (z : ℂ) :
    (fun q : ℝ => mathieuSe m z q - (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  rcases (show m = 3 ∨ m = 4 ∨ m = 5 ∨ 6 ≤ m by omega) with h | h | h | h
  · exact p3q_se3 h z
  · exact p3q_se4 h z
  · exact p3q_se5 h z
  · exact p3q_se_ge6 h z

/-- **Radii of convergence** (DLMF §28.6(ii)): the power series in `q` of `ce_n(z, q)` (for each
fixed `z`) has the same radius of convergence as that of `a_n(q)`; stated as: `a_n` extends
analytically from `(-r, r)` to the disc `|q| < r` iff, for every `z`, `q ↦ ce_n(z, q)` does. -/
@[dlmf 28.6.ii]
theorem mathieuCe_radius_eq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → F q = mathieuA n q) ↔
      ∀ z : ℂ, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → G q = mathieuCe n z q := by
  sorry

/-- **Radii of convergence** (DLMF §28.6(ii)) for `se_n` and `b_n`, `n ≥ 1`. -/
@[dlmf 28.6.ii]
theorem mathieuSe_radius_eq {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) :
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → F q = mathieuB n q) ↔
      ∀ z : ℂ, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → G q = mathieuSe n z q := by
  sorry

end DLMF.Mathieu
