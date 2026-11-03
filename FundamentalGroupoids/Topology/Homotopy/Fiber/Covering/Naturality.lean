/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Covering

/-!
# Naturality of the covering-fiber comparison

A continuous commuting square intertwines the constant-path inclusion, the whole
reverse-path lift, the strict-fiber retraction, and the whole fixing deformation.
The strict-fiber map is the restriction/inclusion composite, and the homotopy-fiber
map is `ContinuousMap.HomotopyFiber.map`; both retain the original maps and topologies.
The deformation square includes the entire retained continuous path, not only its
moving endpoint. Reversing and evaluating the retained path also commutes with the
homotopy-fiber map as an equality of continuous maps on the whole time product.

The inclusion and reversed-path-family squares need no covering hypotheses. The
lift, retraction and deformation squares require only that the source and target
vertical maps are coverings; the horizontal maps are arbitrary continuous maps.
The four space universes are independent, with no connectedness, local compactness,
separation, surjectivity or nonempty-fiber hypotheses.

## References

The comparison maps and their characteristic laws are from
`FundamentalGroupoids.Topology.Homotopy.Fiber.Covering`; the homotopy-fiber map is
from `FundamentalGroupoids.Topology.Homotopy.Fiber`. The reverse-path lift uses
Mathlib's canonical `IsCoveringMap.liftHomotopy`, and its naturality uses Mathlib's
covering-lift uniqueness theorem `IsCoveringMap.eq_of_comp_eq`.
-/

@[expose] public section

open unitInterval
open scoped Topology

section

namespace ContinuousMap.HomotopyFiber

universe uE uB uE' uB'

variable {E : Type uE} {B : Type uB} {E' : Type uE'} {B' : Type uB'}
variable [TopologicalSpace E] [TopologicalSpace B]
variable [TopologicalSpace E'] [TopologicalSpace B']
variable {f : C(E, B)} {g : C(E', B')} {b : B} {b' : B'}

/-- The whole reversed retained-path family commutes with the homotopy-fiber map
of a continuous commuting square. -/
theorem reversePathFamily_naturality
    (a : C(E, E')) (c : C(B, B'))
    (w : ∀ e, g (a e) = c (f e)) (hb : c b = b') :
    (reversePathFamily g b').comp
        ((ContinuousMap.id I).prodMap (map a c w hb)) =
      c.comp (reversePathFamily f b) := by
  apply ContinuousMap.ext
  rintro ⟨t, z⟩
  simp only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    Prod.map_apply, ContinuousMap.id_apply, reversePathFamily_apply, path_map]

end ContinuousMap.HomotopyFiber

end

universe uE uB uE' uB' uP

namespace ContinuousMap.HomotopyFiber

variable {E : Type uE} {B : Type uB} {E' : Type uE'} {B' : Type uB'}
variable [TopologicalSpace E] [TopologicalSpace B]
variable [TopologicalSpace E'] [TopologicalSpace B']
variable (f : C(E, B)) (g : C(E', B')) (a : C(E, E')) (c : C(B, B'))
variable (w : ∀ e, g (a e) = c (f e)) {b : B} {b' : B'} (hb : c b = b')

/-- The constant-path inclusion commutes with a continuous square, without
covering hypotheses. The strict-fiber map is the stock restriction/inclusion. -/
theorem fiberInclusion_naturality :
    (map (f := f) (f' := g) a c w hb).comp (fiberInclusion f b) =
      (fiberInclusion g b').comp
        ((a.restrictPreimage {e' : E' | g e' = b'}).comp
          (ContinuousMap.inclusion
            (show {e : E | f e = b} ⊆ a ⁻¹' {e' : E' | g e' = b'} from
              fun e he => (w e).trans ((congrArg c he).trans hb)))) := by
  apply ContinuousMap.ext
  rintro ⟨e, he⟩
  change map (f := f) (f' := g) a c w hb (fiberInclusion f b ⟨e, he⟩) =
    fiberInclusion g b' ⟨a e, (w e).trans ((congrArg c he).trans hb)⟩
  simpa only [fiberInclusion_apply] using
    (map_const (f := f) (f' := g) a c w hb e he)

/-- The whole jointly continuous reverse-path lift commutes with a continuous
square between coverings. -/
theorem reversePathLift_naturality (covf : IsCoveringMap f) (covg : IsCoveringMap g) :
    a.comp (reversePathLift (f := f) (b := b) covf) =
      (reversePathLift (f := g) (b := b') covg).comp
        ((ContinuousMap.id I).prodMap (map (f := f) (f' := g) a c w hb)) := by
  apply ContinuousMap.ext
  rintro ⟨t, z⟩
  have h : (fun s : I => a (reversePathLift covf (s, z))) =
      (fun s : I => reversePathLift covg (s, map a c w hb z)) := by
    refine covg.eq_of_comp_eq ?_ ?_ ?_ (0 : I) ?_
    · exact a.continuous.comp
        ((reversePathLift covf).continuous.comp (continuous_id.prodMk continuous_const))
    · exact (reversePathLift covg).continuous.comp
        (continuous_id.prodMk continuous_const)
    · funext s
      change g (a (reversePathLift covf (s, z))) =
        g (reversePathLift covg (s, map a c w hb z))
      rw [w, reversePathLift_lifts, reversePathLift_lifts, path_map,
        ContinuousMap.comp_apply]
    · simp only [reversePathLift_zero, point_map]
  simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    Prod.map_apply, ContinuousMap.id_apply] using congr_fun h t

/-- The canonical retraction commutes with a continuous square between coverings,
using the original strict subtype fibers. -/
theorem fiberRetraction_naturality (covf : IsCoveringMap f) (covg : IsCoveringMap g) :
    ((a.restrictPreimage {e' : E' | g e' = b'}).comp
        (ContinuousMap.inclusion
          (show {e : E | f e = b} ⊆ a ⁻¹' {e' : E' | g e' = b'} from
            fun e he => (w e).trans ((congrArg c he).trans hb)))).comp
        (fiberRetraction (f := f) (b := b) covf) =
      (fiberRetraction (f := g) (b := b') covg).comp
        (map (f := f) (f' := g) a c w hb) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change a (fiberRetraction covf z : E) =
    (fiberRetraction covg (map (f := f) (f' := g) a c w hb z) : E')
  rw [fiberRetraction_coe, fiberRetraction_coe]
  simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    Prod.map_apply, ContinuousMap.id_apply] using
    ContinuousMap.congr_fun (reversePathLift_naturality f g a c w hb covf covg) (1, z)

/-- The whole fixing deformation commutes with a continuous square between
coverings, including its entire retained continuous path. -/
theorem fiberDeformation_naturality (covf : IsCoveringMap f) (covg : IsCoveringMap g) :
    (map (f := f) (f' := g) a c w hb).comp
        (fiberDeformation (f := f) (b := b) covf) =
      (fiberDeformation (f := g) (b := b') covg).comp
        ((ContinuousMap.id I).prodMap (map (f := f) (f' := g) a c w hb)) := by
  apply ContinuousMap.ext
  rintro ⟨u, z⟩
  change map (f := f) (f' := g) a c w hb (fiberDeformation covf (u, z)) =
    fiberDeformation covg (u, map (f := f) (f' := g) a c w hb z)
  apply ext
  · rw [point_map, point_fiberDeformation, point_fiberDeformation]
    simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      Prod.map_apply, ContinuousMap.id_apply] using
      ContinuousMap.congr_fun (reversePathLift_naturality f g a c w hb covf covg)
        (unitInterval.symm u, z)
  · rw [path_map]
    apply ContinuousMap.ext
    intro s
    simp only [ContinuousMap.comp_apply, path_fiberDeformation_apply, path_map]

end ContinuousMap.HomotopyFiber
