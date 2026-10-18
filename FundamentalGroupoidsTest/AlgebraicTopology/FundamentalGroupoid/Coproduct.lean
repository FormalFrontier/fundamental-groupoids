/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Coproduct

/-!
# Two one-point summands in the fundamental-groupoid comparison

The family `fun _ : Bool => Unit` uses the stock one-point topology on each summand
and the original sigma topology on their disjoint union. The canonical comparison
keeps the two tagged objects distinct and sends each summand's identity path class,
inserted with the categorical sigma constructor, to the identity at its image.
These controls use only the comparison's constructor API and ordinary functor laws.

For an empty index, both the categorical sigma and the original fundamental groupoid
of the topological sigma have no objects. No default summand or basepoint is chosen.

The final equivalence specialization uses the general comparison theorem.
It is separate from, and is not used by, the independently proved object, identity,
and emptiness properties. No inverse-equivalence data or separate path-lifting
assertion is constructed here.
-/

open CategoryTheory FundamentalGroupoidFunctor

namespace FundamentalGroupoidsTest.Coproduct

/-- The two original tagged objects do not collapse, and their original identity classes
are retained through the canonical sigma-arrow constructor. -/
private theorem two_tag_noncollapse_and_identity_classes :
    let K := sigmaComparison (fun _ : Bool => Unit)
    K.obj ⟨false, FundamentalGroupoid.mk ()⟩ ≠
        K.obj ⟨true, FundamentalGroupoid.mk ()⟩ ∧
      ∀ i : Bool,
        K.map (Sigma.SigmaHom.mk (i := i)
            (𝟙 (FundamentalGroupoid.mk () : FundamentalGroupoid Unit))) =
          𝟙 (K.obj ⟨i, FundamentalGroupoid.mk ()⟩) := by
  dsimp only
  constructor
  · intro h
    have htag : false = true := by
      simpa only [sigmaComparison_obj] using
        congrArg (fun a : FundamentalGroupoid (Σ _ : Bool, Unit) => a.as.1) h
    cases htag
  · intro i
    exact (sigmaComparison (fun _ : Bool => Unit)).map_id ⟨i, FundamentalGroupoid.mk ()⟩

/-- Empty indexing leaves both original endpoint object types empty. -/
private theorem empty_index_has_no_objects :
    IsEmpty (Σ _ : Empty, FundamentalGroupoid Unit) ∧
      IsEmpty (FundamentalGroupoid (Σ _ : Empty, Unit)) := by
  constructor
  · exact ⟨fun a => Empty.elim a.1⟩
  · exact ⟨fun a => Empty.elim a.as.1⟩

/-- The comparison for two one-point summands is an equivalence by specialization of the
general comparison theorem. Unlike the preceding object, identity and emptiness properties,
this is not an independent proof of equivalence. -/
private theorem bool_unit_comparison_isEquivalence :
    (sigmaComparison (fun _ : Bool => Unit)).IsEquivalence := by
  exact sigmaComparison_isEquivalence (fun _ : Bool => Unit)

end FundamentalGroupoidsTest.Coproduct
