/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.FundamentalGroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic.NormNum

/-!
# Moving a nonidentity circle loop

On `AddCircle (1 : ℝ)`, translation by the half-period is homotopic to the
identity through `H(t, z) = z + [t / 2]`. Its track at zero moves to a distinct
basepoint. A nonidentity loop is chosen using Mathlib's equivalence between the
fundamental group and the opposite of the multiplicative form of the covering
group `ℤ ∙ (1 : ℝ)`. No orientation of this loop is asserted.

The two clients compare the translated loop with its transported class and
then map that transported class once more. They use both pointwise and bundled
comparison laws, and retain a nonidentity class throughout. Nonidentity refers
to these loop classes, not to a transport automorphism; the circle's fundamental
group is abelian. The homotopy-retraction client recovers the same nonidentity
loop along the reverse moving track.

## References

* Mathlib's `Topology.Covering.AddCircle` supplies the quotient covering map;
  `Topology.Homotopy.Lifting` supplies its fundamental-group equivalence.
* `Analysis.Convex.Contractible` supplies contractibility of the real line.
-/

noncomputable section

open FundamentalGroup
open scoped unitInterval

namespace CircleTransport

/-- The real circle with period one. -/
abbrev A := AddCircle (1 : ℝ)

/-- The point represented by half a period. -/
def half : A := ((1 / 2 : ℝ) : A)

/-- Translation by half a period. -/
def translation : C(A, A) :=
  ⟨fun z => z + half, continuous_id.add continuous_const⟩

/-- Translation through a continuously varying fraction of a period. -/
def translationHomotopy : ContinuousMap.Homotopy (ContinuousMap.id A) translation where
  toFun p := p.2 + (((p.1 : ℝ) / 2 : ℝ) : A)
  continuous_toFun := continuous_snd.add
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_subtype_val.comp continuous_fst).div_const 2))
  map_zero_left z := by
    change z + (((0 : ℝ) / 2 : ℝ) : A) = z
    norm_num
  map_one_left z := rfl

/-- The basepoint track, from zero to its translate. -/
def halfPath : Path (0 : A) (translation 0) := translationHomotopy.evalAt 0

/-- The track at zero has the explicit value `[t / 2]`. -/
theorem halfPath_apply (t : I) :
    halfPath t = (((t : ℝ) / 2 : ℝ) : A) := by
  change (0 : A) + (((t : ℝ) / 2 : ℝ) : A) = _
  exact zero_add _

/-- Half a period is not zero in the circle. -/
theorem half_ne_zero : half ≠ (0 : A) := by
  intro h
  have hreal : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ))
      (a := (1 / 2 : ℝ)) (by constructor <;> norm_num)).mp h
  norm_num at hreal

/-- The homotopy does not fix the basepoint. -/
theorem translation_zero_ne_zero : translation 0 ≠ (0 : A) := by
  simpa only [translation, ContinuousMap.coe_mk, zero_add] using half_ne_zero

private abbrev CoveringGroup := AddSubgroup.zmultiples (1 : ℝ)

private def deckStep : (Multiplicative CoveringGroup)ᵐᵒᵖ :=
  MulOpposite.op (Multiplicative.ofAdd ⟨1, AddSubgroup.mem_zmultiples (1 : ℝ)⟩)

private theorem deckStep_ne_one : deckStep ≠ 1 := by
  intro h
  have hreal : (1 : ℝ) = 0 := congrArg
    (fun u : (Multiplicative CoveringGroup)ᵐᵒᵖ =>
      ((Multiplicative.toAdd u.unop : CoveringGroup) : ℝ)) h
  exact one_ne_zero hreal

private def coveringCoordinate :
    FundamentalGroup A 0 ≃* (Multiplicative CoveringGroup)ᵐᵒᵖ :=
  (AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv ⟨0, rfl⟩

/-- A loop class chosen as the preimage of a nonunit covering-group element.
This choice does not specify a once-around orientation. -/
def loopClass : FundamentalGroup A 0 := coveringCoordinate.symm deckStep

/-- The chosen loop is not nullhomotopic. -/
theorem loopClass_ne_one : loopClass ≠ 1 := by
  intro h
  apply deckStep_ne_one
  apply coveringCoordinate.symm.injective
  simpa only [loopClass, map_one] using h

/-- Transport to the distinct basepoint preserves the nonidentity class. -/
theorem transported_loopClass_ne_one :
    fundamentalGroupMulEquivOfPath halfPath loopClass ≠ 1 := by
  intro h
  apply loopClass_ne_one
  apply (fundamentalGroupMulEquivOfPath halfPath).injective
  exact h.trans (fundamentalGroupMulEquivOfPath halfPath).map_one.symm

/-- Translation carries the chosen loop to its transport along the moving basepoint,
and the resulting class is not the identity. -/
theorem translated_loopClass :
    fundamentalGroupMulEquivOfPath halfPath loopClass = map translation 0 loopClass ∧
      map translation 0 loopClass ≠ 1 := by
  have hpoint := fundamentalGroupMulEquivOfPath_map_of_homotopy
    translationHomotopy 0 loopClass
  have hhom : (fundamentalGroupMulEquivOfPath halfPath).toMonoidHom =
      map translation 0 := by
    have hcomp :=
      fundamentalGroupMulEquivOfPath_comp_map_of_homotopy translationHomotopy 0
    simp only [map_id] at hcomp
    change (fundamentalGroupMulEquivOfPath halfPath).toMonoidHom.comp
      (MonoidHom.id (FundamentalGroup A 0)) = map translation 0 at hcomp
    exact (MonoidHom.comp_id
      (fundamentalGroupMulEquivOfPath halfPath).toMonoidHom).symm.trans hcomp
  refine ⟨?_, ?_⟩
  · simp only [map_id] at hpoint
    change fundamentalGroupMulEquivOfPath halfPath loopClass =
      map translation 0 loopClass at hpoint
    exact hpoint
  · rw [← hhom]
    exact transported_loopClass_ne_one

/-- Mapping the transported class by the same translation agrees with transport
along the translated track, applied to the first transported class. This second
class is still nonidentity. -/
theorem translation_transport_square :
    map translation (translation 0) (fundamentalGroupMulEquivOfPath halfPath loopClass) =
        fundamentalGroupMulEquivOfPath (halfPath.map translation.continuous)
          (fundamentalGroupMulEquivOfPath halfPath loopClass) ∧
      map translation (translation 0)
        (fundamentalGroupMulEquivOfPath halfPath loopClass) ≠ 1 := by
  have hpoint := map_fundamentalGroupMulEquivOfPath translation halfPath loopClass
  have hhom := map_comp_fundamentalGroupMulEquivOfPath translation halfPath
  constructor
  · exact hpoint.trans (congrArg
      (fundamentalGroupMulEquivOfPath (halfPath.map translation.continuous))
        translated_loopClass.1.symm)
  · intro h
    have heval := congrArg (fun k => k loopClass) hhom
    have hm : fundamentalGroupMulEquivOfPath (halfPath.map translation.continuous)
        (map translation 0 loopClass) = 1 := heval.symm.trans h
    apply translated_loopClass.2
    apply (fundamentalGroupMulEquivOfPath (halfPath.map translation.continuous)).injective
    exact hm.trans
      (fundamentalGroupMulEquivOfPath (halfPath.map translation.continuous)).map_one.symm

/-- A constant homotopy gives no change on the same nonidentity loop class. -/
theorem constant_homotopy_loopClass :
    fundamentalGroupMulEquivOfPath
      ((ContinuousMap.Homotopy.refl (ContinuousMap.id A)).evalAt 0) loopClass = loopClass := by
  have h := fundamentalGroupMulEquivOfPath_map_of_homotopy
    (ContinuousMap.Homotopy.refl (ContinuousMap.id A)) 0 loopClass
  simp only [map_id] at h
  change fundamentalGroupMulEquivOfPath
    ((ContinuousMap.Homotopy.refl (ContinuousMap.id A)).evalAt 0) loopClass = loopClass at h
  exact h

/-- The retraction induced by the reversed translation homotopy recovers the
chosen nonidentity loop. Its basepoint track runs from the distinct translate back
to zero, so this uses a genuinely moving track rather than a based homotopy. -/
theorem retraction_recovers_loopClass :
    retractionOfHomotopy translation (ContinuousMap.id A) translationHomotopy.symm 0
        (map translation 0 loopClass) = loopClass ∧
      retractionOfHomotopy translation (ContinuousMap.id A) translationHomotopy.symm 0
        (map translation 0 loopClass) ≠ 1 := by
  have h := leftInverse_retractionOfHomotopy translation (ContinuousMap.id A)
    translationHomotopy.symm 0 loopClass
  refine ⟨h, ?_⟩
  rw [h]
  exact loopClass_ne_one

end CircleTransport
