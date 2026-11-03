/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Lifting

/-!
# Naturality of covering homotopy lifts

Postcomposition by a continuous commuting square between covering maps commutes
with the canonical homotopy lift. The equality is between whole bundled continuous
maps on the time-parameter product. The parameter space is an arbitrary topological
space, in a universe independent of the four total and base spaces.

Only the two vertical maps must be coverings; the horizontal maps are arbitrary
continuous maps. No connectedness, local compactness, separation, surjectivity or
nonempty-fiber hypotheses are imposed.

## References

This theorem uses Mathlib's canonical `IsCoveringMap.liftHomotopy` and its
uniqueness characterization `IsCoveringMap.eq_liftHomotopy_iff'`, re-exported by
`FundamentalGroupoids.Topology.Covering.Lifting`. Parameter precomposition is
already supplied by `IsCoveringMap.liftHomotopy_comp_prodMap`.
-/

@[expose] public section

open unitInterval
open scoped Topology

universe uE uB uE' uB' uP

namespace IsCoveringMap

/-- Postcomposition of the canonical homotopy lift under a continuous square
between coverings, with an arbitrary topological parameter space. -/
theorem liftHomotopy_naturality
    {E : Type uE} {B : Type uB} {E' : Type uE'} {B' : Type uB'} {P : Type uP}
    [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace B'] [TopologicalSpace P]
    {p : E → B} {p' : E' → B'} (cov : IsCoveringMap p) (cov' : IsCoveringMap p')
    (a : C(E, E')) (c : C(B, B')) (w : ∀ e, p' (a e) = c (p e))
    (H : C(I × P, B)) (q : C(P, E)) (h0 : ∀ x, H (0, x) = p (q x)) :
    a.comp (cov.liftHomotopy H q h0) =
      cov'.liftHomotopy (c.comp H) (a.comp q)
        (fun x => (congrArg c (h0 x)).trans ((w (q x)).symm)) := by
  apply (cov'.eq_liftHomotopy_iff'
    (H := c.comp H) (f := a.comp q)
    (fun x => (congrArg c (h0 x)).trans ((w (q x)).symm))
    (a.comp (cov.liftHomotopy H q h0))).2
  constructor
  · funext tx
    change p' (a (cov.liftHomotopy H q h0 tx)) = c (H tx)
    rw [w]
    exact congrArg c (congr_fun (cov.liftHomotopy_lifts H q h0) tx)
  · intro x
    change a (cov.liftHomotopy H q h0 (0, x)) = a (q x)
    rw [cov.liftHomotopy_zero H q h0 x]

end IsCoveringMap
