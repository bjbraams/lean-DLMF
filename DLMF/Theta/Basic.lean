/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Theta.Basic.Definitions

/-!
# Theta functions: definitions and periodic properties (DLMF §§20.1–20.2)

The project's theta functions are `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`
(`θⱼ(z|τ)` in DLMF normalization, defined from Mathlib's `jacobiTheta₂`; `q = e^{iπτ}`,
period `π` in `z`). As in Mathlib, they are totalized: for `Im τ ≤ 0` they vanish.

This module adds

* the nome forms `jacobiThetaOneQ … jacobiThetaFourQ` (`θⱼ(z,q)`, DLMF §20.1), defined by their
  Fourier series in `q`. DLMF's convention `q^α = e^{iαπτ}` presupposes a known `τ`; for `θ₁, θ₂`
  we use the principal `q^{1/4}`, so `θⱼ(z, e^{iπτ}) = θⱼ(z|τ)` holds for `-1 < Re τ ≤ 1`
  (`jacobiThetaTwoQ_cexp`), while for `θ₃, θ₄` it holds for every `τ`;
* the theta constants `θⱼ(0|τ)`, `θ₁'(0|τ)` (`…NullTau`, `…DerivNullTau`) and their nome forms;
* the Fourier series 20.2.1–20.2.4 in DLMF's sine/cosine form, the lattice quasi-periodicity
  20.2.6–20.2.9, the half-period translations 20.2.10–20.2.14 and the `z`-zeros of §20.2(iv).

Statements are given in the lattice-parameter form `θⱼ(z|τ)`, which avoids the branch of `q^{1/4}`;
results with `q²`, `iq`, … are stated with `2τ`, `τ + 1/2`, … accordingly.

The series, periodicity and zero theorems are in `DLMF.Theta.SeriesAndZeros`.
-/
