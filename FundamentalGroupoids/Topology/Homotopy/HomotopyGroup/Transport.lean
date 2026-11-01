/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Basepoint
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.BoundaryHomotopy
public import FundamentalGroupoids.Topology.Homotopy.Cube.Comparison
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.BoundaryPath

/-!
# Characterizing basepoint transport by moving-boundary homotopies

`HomotopyGroup.pathMap_mk_eq_iff` characterizes equality with a transported
homotopy class: the original cube maps admit a homotopy whose value at every
boundary point follows the prescribed path of basepoints.

For finite coordinate types, two homotopies with the same initial map and
boundary trace agree on the bottom and sides of their cylinders. The cylinder
comparison gives a boundary-relative homotopy between their final maps.
Conversely, append a boundary-relative homotopy to the transport homotopy and
remove the constant final segment from its boundary trace by a path homotopy.
For infinite coordinate types, every homotopy group is a subsingleton and the
moving-boundary homotopy exists between any two generalized loops.

The coordinate type and target have independent universes. Empty coordinate
types are included, and the target requires only a topology.

## References

* `Cube.cylinderComparisonTop` supplies the finite-cylinder comparison.
* Mathlib's `GenLoop.Homotopic` and quotient APIs supply equality of homotopy
  classes; its `Path.Homotopic.trans_refl` supplies the path right-unit law.
-/

public section

universe u v

open scoped unitInterval

namespace HomotopyGroup

variable {N : Type u} {X : Type v} [TopologicalSpace X] {x y : X}

private theorem homotopic_pathMap_of_boundary [Finite N] (γ : Path x y)
    (p : GenLoop N X x) (q : GenLoop N X y)
    (H : ContinuousMap.Homotopy p.val q.val)
    (hH : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t) :
    GenLoop.Homotopic (GenLoop.pathMap γ p) q := by
  let F : C(Unit × (I × (N → I)), X) :=
    (GenLoop.homotopyAlong γ p).toContinuousMap.comp ContinuousMap.snd
  let G : C(Unit × (I × (N → I)), X) :=
    H.toContinuousMap.comp ContinuousMap.snd
  have hFG : Set.EqOn F G {r | r.2 ∈ Cube.bottomSides N} := by
    rintro ⟨_, t, z⟩ hr
    rcases (Cube.mem_bottomSides (t, z)).mp hr with ht | hz
    · change t = 0 at ht
      subst t
      change GenLoop.homotopyAlong γ p (0, z) = H (0, z)
      exact ((GenLoop.homotopyAlong γ p).map_zero_left z).trans
        (H.map_zero_left z).symm
    · change GenLoop.homotopyAlong γ p (t, z) = H (t, z)
      exact (GenLoop.homotopyAlong_boundary γ p t z hz).trans (hH t z hz).symm
  let j : C(N → I, Unit × (N → I)) :=
    (ContinuousMap.const (N → I) ()).prodMk (ContinuousMap.id (N → I))
  have hj : Set.MapsTo j (Cube.boundary N)
      {r : Unit × (N → I) | r.2 ∈ Cube.boundary N} := fun _ hz ↦ hz
  have hF : (Cube.restrictCylinderTop F).comp j = (GenLoop.pathMap γ p).val := by
    apply ContinuousMap.ext
    intro z
    change GenLoop.homotopyAlong γ p (1, z) = (GenLoop.pathMap γ p).val z
    exact (GenLoop.homotopyAlong γ p).map_one_left z
  have hG : (Cube.restrictCylinderTop G).comp j = q.val := by
    apply ContinuousMap.ext
    intro z
    change H (1, z) = q.val z
    exact H.map_one_left z
  exact ⟨((Cube.cylinderComparisonTop F G hFG).precomp j hj).cast hF hG⟩

/-- Equality with the class transported along `γ` is equivalent to a homotopy
of the original cube maps whose boundary follows `γ` at every time. This holds
for arbitrary coordinate types, including empty and infinite types. -/
theorem pathMap_mk_eq_iff (γ : Path x y) (p : GenLoop N X x) (q : GenLoop N X y) :
    pathMap γ (⟦p⟧ : HomotopyGroup N X x) = (⟦q⟧ : HomotopyGroup N X y) ↔
      Nonempty {H : ContinuousMap.Homotopy p.val q.val //
        ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t} := by
  classical
  rcases finite_or_infinite N with hN | hN
  · let : Finite N := hN
    rw [pathMap_class]
    constructor
    · intro hpq
      obtain ⟨K⟩ := (Quotient.exact hpq : GenLoop.Homotopic (GenLoop.pathMap γ p) q)
      have hcanon : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N →
          GenLoop.homotopyAlong γ p (t, z) = γ t :=
        GenLoop.homotopyAlong_boundary γ p
      have hrel : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N →
          K.toHomotopy (t, z) = (Path.refl y) t := by
        intro t z hz
        exact (K.eq_fst t hz).trans (GenLoop.boundary (GenLoop.pathMap γ p) z hz)
      have htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N →
          ((GenLoop.homotopyAlong γ p).trans K.toHomotopy) (t, z) =
            (γ.trans (Path.refl y)) t := by
        intro t z hz
        exact GenLoop.homotopy_trans_boundary
          (GenLoop.homotopyAlong γ p) K.toHomotopy hcanon hrel t z hz
      obtain ⟨H, hH⟩ :=
        (GenLoop.exists_homotopy_boundary_iff_of_homotopic
          (p := p) (q := q) (Path.Homotopic.trans_refl γ)).mp
            ⟨(GenLoop.homotopyAlong γ p).trans K.toHomotopy, htrace⟩
      exact ⟨⟨H, hH⟩⟩
    · rintro ⟨⟨H, hH⟩⟩
      exact Quotient.sound (homotopic_pathMap_of_boundary γ p q H hH)
  · let : Infinite N := hN
    let : Subsingleton (HomotopyGroup N X y) := subsingleton_of_infinite N X y
    constructor
    · intro _
      exact ⟨⟨GenLoop.homotopyAlongOfInfinite γ p q,
        fun t _ hz ↦ GenLoop.homotopyAlongOfInfinite_boundary γ p q t hz⟩⟩
    · intro _
      exact Subsingleton.elim _ _

end HomotopyGroup
