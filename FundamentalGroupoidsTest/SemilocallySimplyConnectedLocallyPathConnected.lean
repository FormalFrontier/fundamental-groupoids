/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.SemilocallySimplyConnected.LocallyPathConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Uniform ambient null-loop neighborhoods in the real line

The simply connected real line is locally path connected. At zero, the
semilocal refinement gives one open path-connected neighborhood whose loops
at every point contract in the ambient real line.
-/

example :
    ∃ V : Set ℝ, IsOpen V ∧ (0 : ℝ) ∈ V ∧ IsPathConnected V ∧
      ∀ y ∈ V, ∀ γ : Path y y, Set.range γ ⊆ V → γ.Homotopic (Path.refl y) :=
  (isSemilocallySimplyConnectedAt (0 : ℝ)).exists_isOpen_isPathConnected
