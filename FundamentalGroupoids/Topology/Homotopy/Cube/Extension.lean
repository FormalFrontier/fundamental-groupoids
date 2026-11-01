/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube.Deformation
public import Mathlib.Topology.ContinuousOn

/-!
# Homotopy extension for finite cubes

`Cube.homotopyExtension` extends compatible data on the bottom and sides of a
finite-dimensional cylinder. The data may depend jointly and continuously on
an arbitrary parameter space. No separation or local compactness assumptions
on the parameter or target space are required, and the coordinate type may be
empty.

The construction first pastes the given maps on the bottom and sides, using
Mathlib's `ContinuousOn.union_of_isClosed`. It then composes with
`Cube.cylinderRetraction`. Closedness of the sides uses
`Cube.isClosed_boundary`, so no ambient extension of the side data is needed.
-/

public section

noncomputable section

universe u v w

open scoped unitInterval

namespace Cube

variable {N : Type u} {P : Type v} {X : Type w}
  [TopologicalSpace P] [TopologicalSpace X]

variable (f : C(P × (N → I), X)) (g : C(P × (I × boundary N), X))

private def extensionValue (q : P × bottomSides N) : X := by
  classical
  exact if ht : q.2.val.1 = 0 then
    f (q.1, q.2.val.2)
  else
    g (q.1, (q.2.val.1,
      ⟨q.2.val.2, ((mem_bottomSides _).mp q.2.property).resolve_left ht⟩))

private theorem extensionValue_of_zero (q : P × bottomSides N)
    (hq : q.2.val.1 = 0) :
    extensionValue f g q = f (q.1, q.2.val.2) := by
  simp only [extensionValue, dite_eq_left hq]

private theorem extensionValue_of_boundary
    (h0 : ∀ (p : P) (a : boundary N), g (p, (0, a)) = f (p, a.val))
    (q : P × bottomSides N) (hq : q.2.val.2 ∈ boundary N) :
    extensionValue f g q = g (q.1, (q.2.val.1, ⟨q.2.val.2, hq⟩)) := by
  by_cases ht : q.2.val.1 = 0
  · rw [extensionValue_of_zero f g q ht]
    simpa only [ht] using (h0 q.1 ⟨q.2.val.2, hq⟩).symm
  · simp only [extensionValue, dite_eq_right ht]

variable [Finite N]

private def extensionOnBottomSides
    (h0 : ∀ (p : P) (a : boundary N), g (p, (0, a)) = f (p, a.val)) :
    C(P × bottomSides N, X) where
  toFun := extensionValue f g
  continuous_toFun := by
    let A : Set (P × bottomSides N) := {q | q.2.val.1 = 0}
    let B : Set (P × bottomSides N) := {q | q.2.val.2 ∈ boundary N}
    have hA : IsClosed A :=
      isClosed_eq
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) continuous_const
    have hB : IsClosed B := by
      change IsClosed {q : P × bottomSides N | q.2.val.2 ∈ boundary N}
      exact (isClosed_boundary N).preimage
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
    have hbot : ContinuousOn (extensionValue f g) A := by
      apply (f.continuous.comp
        (continuous_fst.prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))).continuousOn.congr
      intro q hq
      exact extensionValue_of_zero f g q hq
    have hside : ContinuousOn (extensionValue f g) B := by
      rw [continuousOn_iff_continuous_domRestrict]
      let k : B → P × (I × boundary N) := fun q =>
        (q.val.1, (q.val.2.val.1, ⟨q.val.2.val.2, q.property⟩))
      have hk : Continuous k := by
        dsimp only [k]
        fun_prop
      exact (g.continuous.comp hk).congr fun q =>
        (extensionValue_of_boundary f g h0 q.val q.property).symm
    apply continuousOn_univ.mp
    apply (hbot.union_of_isClosed hside hA hB).mono
    intro q _
    exact (mem_bottomSides q.2.val).mp q.2.property

/-- Extend a jointly continuous family of maps on a finite cube along a jointly
continuous homotopy on its boundary. The prescribed data agree at time zero;
the extension retains both the initial map and the entire boundary homotopy. -/
def homotopyExtension
    (h0 : ∀ (p : P) (a : boundary N), g (p, (0, a)) = f (p, a.val)) :
    C(P × (I × (N → I)), X) :=
  (extensionOnBottomSides f g h0).comp
    { toFun := fun q => (q.1, cylinderRetraction N q.2)
      continuous_toFun :=
        continuous_fst.prodMk ((cylinderRetraction N).continuous.comp continuous_snd) }

/-- At time zero the homotopy extension is the prescribed cube map. -/
@[simp]
theorem homotopyExtension_apply_zero
    (h0 : ∀ (p : P) (a : boundary N), g (p, (0, a)) = f (p, a.val))
    (p : P) (z : N → I) :
    homotopyExtension f g h0 (p, (0, z)) = f (p, z) := by
  change extensionOnBottomSides f g h0 (p, cylinderRetraction N (0, z)) = _
  rw [cylinderRetraction_subtype N ⟨(0, z), Or.inl rfl⟩]
  exact extensionValue_of_zero f g (p, ⟨(0, z), Or.inl rfl⟩) rfl

/-- On the boundary the homotopy extension is the prescribed homotopy. -/
@[simp]
theorem homotopyExtension_boundary
    (h0 : ∀ (p : P) (a : boundary N), g (p, (0, a)) = f (p, a.val))
    (p : P) (t : I) (a : boundary N) :
    homotopyExtension f g h0 (p, (t, a.val)) = g (p, (t, a)) := by
  change extensionOnBottomSides f g h0 (p, cylinderRetraction N (t, a.val)) = _
  rw [cylinderRetraction_subtype N ⟨(t, a.val), Or.inr a.property⟩]
  exact extensionValue_of_boundary f g h0
    (p, ⟨(t, a.val), Or.inr a.property⟩) a.property

end Cube
