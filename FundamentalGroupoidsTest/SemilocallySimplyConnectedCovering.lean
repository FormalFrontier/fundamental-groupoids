/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.SemilocallySimplyConnected.Maps
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Covering.AddCircle

/-!
# Semilocal simple connectivity of the circle

The quotient covering from the simply connected real line onto `AddCircle (1 : ℝ)`
gives semilocal simple connectivity of the circle, pointwise and globally. The
global conclusion also follows from surjective local-homeomorphism descent.
These are semilocal conclusions, not assertions that the circle is simply connected.
-/

@[expose] public section

private theorem realCircle_surjective :
    Function.Surjective ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  QuotientAddGroup.mk_surjective

example (x : ℝ) : IsSemilocallySimplyConnectedAt (x : AddCircle (1 : ℝ)) :=
  ((AddCircle.isCoveringMap_coe (1 : ℝ)).isSemilocallySimplyConnectedAt_iff x).mp
    (isSemilocallySimplyConnectedAt x)

example : SemilocallySimplyConnectedSpace (AddCircle (1 : ℝ)) :=
  (AddCircle.isCoveringMap_coe (1 : ℝ)).semilocallySimplyConnectedSpace_of_surjective
    realCircle_surjective

example : SemilocallySimplyConnectedSpace (AddCircle (1 : ℝ)) :=
  (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).semilocallySimplyConnectedSpace_of_surjective
    realCircle_surjective
