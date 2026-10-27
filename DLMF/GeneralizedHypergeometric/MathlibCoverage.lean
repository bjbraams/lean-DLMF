/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-! # Checked upstream pointers for DLMF Chapter16

The power-series APIs are distinguished from principal analytic continuation.
Existing project theorems are recorded separately in the chapter acquisition ledger; root
attaches missing native tags rather than registering local declarations as upstream.
-/

dlmf_upstream 16.2.E1 Complex.regularizedHGFunCoeff "partial: defining coefficients after division by bottom Gamma product"
dlmf_upstream 16.2.E1 Complex.regularizedHGFunSeries "partial: formal multilinear series, including radii"
dlmf_upstream 16.2.E1 Complex.radius_regularizedHGFunSeries_eq_top "exact scaled entire-series radius when p<=q"
dlmf_upstream 16.2.E1 Complex.radius_regularizedHGFunSeries_eq_top_of_finite "exact scaled terminating-series radius for a nonpositive integer upper parameter"
dlmf_upstream 16.2.E1 Complex.radius_regularizedHGFunSeries_eq_one "exact scaled radius when p=q+1 and no terminating upper parameter"
dlmf_upstream 16.2.E1 Complex.hasSum_regularizedHGFun "partial: TauCeti HasSum API for p<=q, every complex z"
dlmf_upstream 16.2.E5 Complex.regularizedHGFun "partial: exact scaled power-series definition; analytic continuation is separate locally"
dlmf_upstream 16.3.E6 Complex.regularizedHGFun_zero_singleton_eq_mul_add_mul "exact regularized 0F1 contiguous identity, all lower parameters; ordinary Gamma adapter acquired locally"
