/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Connected.ZerothHomotopy.HomotopyEquiv
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Covering.Naturality

/-!
# Path components of the homotopy fiber of a covering

For a covering map, the path-component space of its homotopy fiber is
homeomorphic to its strict subtype fiber. The comparison is induced by the
covering-fiber homotopy equivalence and the canonical evaluation of path
components of a discrete space. It preserves the original fiber topologies and
is natural in continuous commuting squares between coverings, including empty
fibers and with no covering assumptions on the horizontal maps.
-/

@[expose] public section

open scoped Topology

universe uE uB uE' uB'

namespace ContinuousMap.HomotopyFiber

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]
variable {f : C(E, B)} {b : B}

/-- Path components of the homotopy fiber of a covering are homeomorphic to
its strict subtype fiber. -/
noncomputable def zerothHomotopyHomeomorphFiber (cov : IsCoveringMap f) :
    ZerothHomotopy (HomotopyFiber f b) ≃ₜ {e : E // f e = b} := by
  letI : Subsingleton (f '' (f ⁻¹' {b})) := ⟨by
    rintro ⟨y, hy⟩ ⟨y', hy'⟩
    apply Subtype.ext
    rcases hy with ⟨e, he, rfl⟩
    rcases hy' with ⟨e', he', rfl⟩
    have h : f e = b := he
    have h' : f e' = b := he'
    exact h.trans h'.symm⟩
  letI : DiscreteTopology (f '' (f ⁻¹' {b})) := inferInstance
  letI : DiscreteTopology {e : E // f e = b} :=
    (cov.isLocalHomeomorph.isLocalHomeomorphOn
      (s := f ⁻¹' {b})).discreteTopology_of_image
  letI : TotallyDisconnectedSpace {e : E // f e = b} := inferInstance
  exact
    (ZerothHomotopy.homeomorphOfHomotopyEquiv
      (fiberHomotopyEquiv (f := f) (b := b) cov)).symm.trans
      (ZerothHomotopy.homeomorphOfTotallyDisconnectedSpace
        (X := {e : E // f e = b}))

/-- The covering comparison evaluates a class using the canonical fiber retraction. -/
theorem zerothHomotopyHomeomorphFiber_apply_mk (cov : IsCoveringMap f)
    (z : HomotopyFiber f b) :
    zerothHomotopyHomeomorphFiber cov (ZerothHomotopy.mk z) = fiberRetraction cov z := by
  have h :
      (ZerothHomotopy.homeomorphOfHomotopyEquiv (fiberHomotopyEquiv cov)).symm
          (ZerothHomotopy.mk z) =
        ZerothHomotopy.mk (fiberRetraction cov z) := by
    change ((ZerothHomotopy.homeomorphOfHomotopyEquiv
      (fiberHomotopyEquiv cov)).toEquiv).symm (ZerothHomotopy.mk z) = _
    rw [ZerothHomotopy.homeomorphOfHomotopyEquiv_toEquiv,
      ZerothHomotopy.equivOfHomotopyEquiv_symm,
      ZerothHomotopy.coe_equivOfHomotopyEquiv, ZerothHomotopy.map_mk,
      fiberHomotopyEquiv_symm_apply]
  simp only [zerothHomotopyHomeomorphFiber, Homeomorph.trans_apply, h,
    ZerothHomotopy.homeomorphOfTotallyDisconnectedSpace_mk]

/-- The inverse covering comparison takes the class of the constant-path inclusion. -/
theorem zerothHomotopyHomeomorphFiber_symm_apply (cov : IsCoveringMap f)
    (e : {e : E // f e = b}) :
    (zerothHomotopyHomeomorphFiber cov).symm e =
      ZerothHomotopy.mk (fiberInclusion f b e) := by
  apply (zerothHomotopyHomeomorphFiber cov).injective
  rw [Homeomorph.apply_symm_apply, zerothHomotopyHomeomorphFiber_apply_mk]
  exact (fiberRetraction_fiberInclusion cov e.1 e.2).symm

variable {E' : Type uE'} {B' : Type uB'}
variable [TopologicalSpace E'] [TopologicalSpace B']
variable {g : C(E', B')} {b' : B'}

/-- The covering comparison commutes with the homotopy-fiber map and the
restriction of the horizontal map to the strict subtype fibers. -/
theorem zerothHomotopyHomeomorphFiber_naturality
    (a : C(E, E')) (c : C(B, B'))
    (w : ∀ e, g (a e) = c (f e)) (hb : c b = b')
    (covf : IsCoveringMap f) (covg : IsCoveringMap g)
    (q : ZerothHomotopy (HomotopyFiber f b)) :
    ((a.restrictPreimage {e' : E' | g e' = b'}).comp
        (ContinuousMap.inclusion
          (show {e : E | f e = b} ⊆ a ⁻¹' {e' : E' | g e' = b'} from
            fun e he => (w e).trans ((congrArg c he).trans hb))))
        (zerothHomotopyHomeomorphFiber covf q) =
      zerothHomotopyHomeomorphFiber covg
        (ZerothHomotopy.map (map (f := f) (f' := g) a c w hb) q) := by
  obtain ⟨z, rfl⟩ := ZerothHomotopy.isQuotientMap_mk.surjective q
  simpa only [ZerothHomotopy.map_mk, zerothHomotopyHomeomorphFiber_apply_mk,
    ContinuousMap.comp_apply] using
      ContinuousMap.congr_fun
        (fiberRetraction_naturality f g a c w hb covf covg) z

end ContinuousMap.HomotopyFiber
