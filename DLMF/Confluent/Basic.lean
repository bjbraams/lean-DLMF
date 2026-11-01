/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Basic.KummerM
public import DLMF.Confluent.Basic.Tricomi
public import DLMF.Confluent.Basic.IncompleteGamma
public import DLMF.Confluent.Basic.ExponentialIntegrals
public import DLMF.Confluent.Basic.ErrorFunctions
public import DLMF.Confluent.Basic.ExpansionData
public import DLMF.Confluent.Basic.Buchholz

/-!
# Confluent hypergeometric functions: foundational definitions

Canonical definitions and normalizations for the confluent area: Kummer's `M`, Tricomi's `U`,
the incomplete gamma functions, exponential integrals, error, Fresnel and Dawson functions,
expansion coefficients, and the coefficients of the Whittaker–Buchholz expansion.
-/
