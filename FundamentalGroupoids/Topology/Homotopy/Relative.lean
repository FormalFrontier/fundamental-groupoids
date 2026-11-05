/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Inseparable

/-!
# Constrained homotopies and mapping spaces

Pointwise specialization gives a homotopy whose time slices are its endpoints,
preserving any predicate satisfied by both endpoints. A point specializing to
every point of a space also yields contractibility of that space.

A homotopy whose intermediate maps satisfy a predicate gives a path in the
corresponding subtype of the compact-open mapping space. For a locally compact
source, uncurrying gives the converse. No local compactness or separation
assumption is needed on the target.

Precomposing a homotopy relative to `S` along a continuous map gives a homotopy
relative to any set mapped into `S`. If the identity deforms onto a subset while
fixing that subset, maps agreeing there admit a relative homotopy, obtained by
postcomposition and concatenation.

Relative homotopies into a dependent product correspond to families of coordinate
relative homotopies on the same source and fixed set. This correspondence preserves
constant homotopies, reversal and concatenation.

## References

* Mathlib's `Mathlib.Topology.Homotopy.Basic` supplies relative homotopies,
  product assembly, currying and precomposition of their underlying homotopies;
  `Mathlib.Topology.CompactOpen` supplies uncurrying, and
  `Mathlib.Topology.Connected.PathConnected` supplies paths in subtypes.
-/

@[expose] public section

noncomputable section

universe u v w

open unitInterval

namespace ContinuousMap

namespace HomotopyWith

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
  {f₀ f₁ : C(A, B)} {P : C(A, B) → Prop}

/-- Pointwise specialization from `f₀` to `f₁` gives a homotopy in the same direction,
with value `f₀` until the final time and value `f₁` at time `1`. Since every time slice
is an endpoint, any predicate holding at both endpoints is preserved. -/
noncomputable def ofSpecializes (h : ∀ a, f₀ a ⤳ f₁ a) (h₀ : P f₀) (h₁ : P f₁) :
    HomotopyWith f₀ f₁ P := by
  classical
  refine
    { toFun := fun p ↦ if p.1 = 1 then f₁ p.2 else f₀ p.2
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · have hs : IsClosed {p : I × A | p.1 = 1} :=
      isClosed_singleton.preimage continuous_fst
    exact hs.continuous_piecewise_of_specializes
      (f₁.continuous.comp continuous_snd) (f₀.continuous.comp continuous_snd)
      (fun p ↦ h p.2)
  · intro a
    simp
  · intro a
    simp
  · intro t
    by_cases ht : t = 1
    · convert h₁ using 1
      ext a
      simp [ht]
    · convert h₀ using 1
      ext a
      simp [ht]

@[simp]
theorem ofSpecializes_apply (h : ∀ a, f₀ a ⤳ f₁ a) (h₀ : P f₀) (h₁ : P f₁)
    (p : I × A) :
    ofSpecializes h h₀ h₁ p = if p.1 = 1 then f₁ p.2 else f₀ p.2 := by
  classical
  rfl

end HomotopyWith

namespace HomotopyRel

section Pi

universe uA uι uX

variable {A : Type uA} [TopologicalSpace A] {ι : Type uι} {X : ι → Type uX}
  [∀ i, TopologicalSpace (X i)]

/-- Relative homotopies into a dependent product are equivalent to families of
coordinate relative homotopies on the same source and fixed set. -/
noncomputable def piEquiv (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A) :
    f₀.HomotopyRel f₁ S ≃
      (∀ i, ((ContinuousMap.eval i).comp f₀).HomotopyRel
        ((ContinuousMap.eval i).comp f₁) S) where
  toFun H i := H.compContinuousMap (ContinuousMap.eval i)
  invFun K :=
    { toHomotopy := (Homotopy.pi (fun i ↦ (K i).toHomotopy)).cast
        (ContinuousMap.ext (fun _ ↦ rfl)) (ContinuousMap.ext (fun _ ↦ rfl))
      prop' t _ ha := funext fun i ↦ (K i).eq_fst t ha }
  left_inv _ := HomotopyWith.ext (fun _ ↦ rfl)
  right_inv _ := funext fun _ ↦ HomotopyWith.ext (fun _ ↦ rfl)

/-- The coordinate of a relative homotopy is its postcomposition with evaluation. -/
@[simp]
theorem piEquiv_apply (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A)
    (H : f₀.HomotopyRel f₁ S) (i : ι) :
    piEquiv f₀ f₁ S H i = H.compContinuousMap (ContinuousMap.eval i) :=
  rfl

/-- Evaluation of a coordinate relative homotopy is the corresponding coordinate
of the original homotopy. -/
theorem piEquiv_apply_apply (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A)
    (H : f₀.HomotopyRel f₁ S) (i : ι) (st : I × A) :
    piEquiv f₀ f₁ S H i st = H st i :=
  rfl

/-- Reconstructing a relative homotopy from its coordinates preserves every value. -/
@[simp]
theorem piEquiv_symm_apply (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A)
    (K : ∀ i, ((ContinuousMap.eval i).comp f₀).HomotopyRel
      ((ContinuousMap.eval i).comp f₁) S) (st : I × A) :
    (piEquiv f₀ f₁ S).symm K st = (fun i ↦ K i st) :=
  rfl

/-- Taking a coordinate preserves the constant relative homotopy. -/
theorem piEquiv_refl (f₀ : C(A, ∀ i, X i)) (S : Set A) (i : ι) :
    piEquiv f₀ f₀ S (ContinuousMap.HomotopyRel.refl f₀ S) i =
      ContinuousMap.HomotopyRel.refl ((ContinuousMap.eval i).comp f₀) S :=
  HomotopyWith.ext (fun st ↦ piEquiv_apply_apply f₀ f₀ S (refl f₀ S) i st)

/-- Taking a coordinate commutes with reversal of homotopy time. -/
theorem piEquiv_symm (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A)
    (H : f₀.HomotopyRel f₁ S) (i : ι) :
    piEquiv f₁ f₀ S H.symm i = (piEquiv f₀ f₁ S H i).symm := by
  apply HomotopyWith.ext
  intro st
  simp only [piEquiv_apply_apply, symm_apply]

/-- Taking a coordinate preserves concatenation with the same homotopy-time clock. -/
theorem piEquiv_trans (f₀ f₁ f₂ : C(A, ∀ i, X i)) (S : Set A)
    (H : f₀.HomotopyRel f₁ S) (G : f₁.HomotopyRel f₂ S) (i : ι) :
    piEquiv f₀ f₂ S (H.trans G) i =
      (piEquiv f₀ f₁ S H i).trans (piEquiv f₁ f₂ S G i) := by
  apply HomotopyWith.ext
  intro st
  simp only [piEquiv_apply_apply, trans_apply]
  split_ifs <;> rfl

end Pi

end HomotopyRel

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace HomotopyWith

variable {f g : C(X, Y)} {P : C(X, Y) → Prop}

/-- A homotopy satisfying a predicate joins its endpoints in the corresponding
subtype of the compact-open mapping space. Currying requires no local compactness. -/
theorem joined (H : HomotopyWith f g P) (hf : P f) (hg : P g) :
    Joined (⟨f, hf⟩ : Subtype P) ⟨g, hg⟩ := by
  apply (joinedIn_iff_joined (F := {k : C(X, Y) | P k}) hf hg).mp
  exact ⟨⟨H.toHomotopy.curry, H.toHomotopy.curry_zero, H.toHomotopy.curry_one⟩,
    H.prop⟩

/-- For a locally compact source, homotopies satisfying a predicate are equivalent
to paths between the endpoints in the corresponding compact-open mapping subtype. -/
theorem nonempty_iff_joined [LocallyCompactSpace X] (hf : P f) (hg : P g) :
    Nonempty (HomotopyWith f g P) ↔ Joined (⟨f, hf⟩ : Subtype P) ⟨g, hg⟩ := by
  constructor
  · rintro ⟨H⟩
    exact H.joined hf hg
  · rintro ⟨γ⟩
    let γ' : Path f g := γ.map continuous_subtype_val
    refine ⟨{ toContinuousMap := γ'.toContinuousMap.uncurry
              map_zero_left := fun a ↦ congrArg (fun k : C(X, Y) ↦ k a) γ'.source
              map_one_left := fun a ↦ congrArg (fun k : C(X, Y) ↦ k a) γ'.target
              prop' := ?_ }⟩
    intro t
    change P (γ t).val
    exact (γ t).property

end HomotopyWith

namespace HomotopyRel

variable {f g : C(X, Y)} {S : Set X} {T : Set Z}

/-- Precompose a homotopy relative to `S` by a continuous map sending `T` into `S`. -/
def precomp (H : HomotopyRel f g S) (k : C(Z, X)) (hk : Set.MapsTo k T S) :
    HomotopyRel (f.comp k) (g.comp k) T where
  toHomotopy := H.toHomotopy.compContinuousMap k
  prop' t _ hz := H.eq_fst t (hk hz)

@[simp]
theorem precomp_toHomotopy (H : HomotopyRel f g S) (k : C(Z, X))
    (hk : Set.MapsTo k T S) :
    (H.precomp k hk).toHomotopy = H.toHomotopy.compContinuousMap k :=
  rfl

@[simp]
theorem precomp_apply (H : HomotopyRel f g S) (k : C(Z, X))
    (hk : Set.MapsTo k T S) (p : I × Z) :
    H.precomp k hk p = H (p.1, k p.2) :=
  rfl

/-- Maps agreeing on a deformation retract are homotopic relative to that subset.
The homotopy follows `H` through `f` and then follows `H` backwards through `g`.
Only the deformation of the source is used; the target is an arbitrary space. -/
def ofEqOnRetraction (r : C(X, S))
    (H : HomotopyRel (ContinuousMap.id X) ((subtypeVal S).comp r) S)
    (f g : C(X, Y)) (hfg : Set.EqOn f g S) : HomotopyRel f g S := by
  have hmid : f.comp ((subtypeVal S).comp r) =
      g.comp ((subtypeVal S).comp r) := by
    ext x
    exact hfg (r x).property
  exact ((H.compContinuousMap f).trans
    ((H.compContinuousMap g).symm.cast hmid.symm rfl)).cast
      (f.comp_id) (g.comp_id)

/-- The comparison uses the first map during the forward deformation and the
second map during the reversed deformation. -/
theorem ofEqOnRetraction_apply (r : C(X, S))
    (H : HomotopyRel (ContinuousMap.id X) ((subtypeVal S).comp r) S)
    (f g : C(X, Y)) (hfg : Set.EqOn f g S) (p : I × X) :
    ofEqOnRetraction r H f g hfg p =
      if h : (p.1 : ℝ) ≤ 1 / 2 then
        f (H (⟨2 * p.1,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨p.1.2.1, h⟩⟩, p.2))
      else
        g (H (σ ⟨2 * p.1 - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, p.1.2.2⟩⟩, p.2)) := by
  simp only [ofEqOnRetraction, cast_apply, trans_apply,
    compContinuousMap_apply, symm_apply]

end HomotopyRel

namespace HomotopicRel

/-- Precomposition preserves relative homotopy on every set mapped into the fixed set. -/
theorem precomp_continuousMap {f₀ f₁ : C(Y, Z)} {S : Set Y} {T : Set X}
    (H : f₀.HomotopicRel f₁ S) (g : C(X, Y)) (hg : Set.MapsTo g T S) :
    (f₀.comp g).HomotopicRel (f₁.comp g) T :=
  H.map (fun F ↦ F.precomp g hg)

end HomotopicRel

end ContinuousMap

/-- A space with a point specializing to every point is contractible. -/
theorem contractibleSpace_of_specializes {Y : Type w} [TopologicalSpace Y]
    (p : Y) (h : ∀ y : Y, p ⤳ y) : ContractibleSpace Y := by
  apply (contractible_iff_id_nullhomotopic Y).mpr
  refine ⟨p, ?_⟩
  exact ⟨(ContinuousMap.HomotopyWith.ofSpecializes
    (f₀ := ContinuousMap.const Y p) (f₁ := ContinuousMap.id Y)
    (P := fun _ ↦ True) h trivial trivial).toHomotopy.symm⟩

namespace ContinuousMap

section PiNaturality

universe uA uι uX uY uκ

variable {A : Type uA} [TopologicalSpace A]
  {ι : Type uι} {X : ι → Type uX} {Y : ι → Type uY}
  [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
  {κ : Type uκ}

namespace HomotopyRel

/-- Taking coordinates of a relative homotopy commutes with coordinatewise
postcomposition, after transporting both endpoint maps. -/
theorem piEquiv_compContinuousMap
    (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A)
    (H : f₀.HomotopyRel f₁ S) (f : ∀ i, C(X i, Y i)) (i : ι) :
    (piEquiv ((ContinuousMap.piMap f).comp f₀)
        ((ContinuousMap.piMap f).comp f₁) S
        (H.compContinuousMap (ContinuousMap.piMap f)) i).cast
      (show (ContinuousMap.eval i : C(∀ j, Y j, Y i)).comp
          ((ContinuousMap.piMap f).comp f₀) =
          (f i).comp ((ContinuousMap.eval i : C(∀ j, X j, X i)).comp f₀) from
        ContinuousMap.ext (fun _ => rfl))
      (show (ContinuousMap.eval i : C(∀ j, Y j, Y i)).comp
          ((ContinuousMap.piMap f).comp f₁) =
          (f i).comp ((ContinuousMap.eval i : C(∀ j, X j, X i)).comp f₁) from
        ContinuousMap.ext (fun _ => rfl)) =
      (piEquiv f₀ f₁ S H i).compContinuousMap (f i) := by
  apply HomotopyWith.ext
  intro st
  simp only [cast_apply, piEquiv_apply_apply, compContinuousMap_apply]
  rfl

/-- Taking coordinates of a relative homotopy commutes with arbitrary reindexing,
after transporting both endpoint maps. -/
theorem piEquiv_reindex
    (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A)
    (H : f₀.HomotopyRel f₁ S) (ρ : κ → ι) (k : κ) :
    (piEquiv ((ContinuousMap.precomp ρ).comp f₀)
        ((ContinuousMap.precomp ρ).comp f₁) S
        (H.compContinuousMap (ContinuousMap.precomp ρ)) k).cast
      (show (ContinuousMap.eval k : C(∀ j : κ, X (ρ j), X (ρ k))).comp
          ((ContinuousMap.precomp ρ).comp f₀) =
          (ContinuousMap.eval (ρ k) : C(∀ j, X j, X (ρ k))).comp f₀ from
        ContinuousMap.ext (fun _ => rfl))
      (show (ContinuousMap.eval k : C(∀ j : κ, X (ρ j), X (ρ k))).comp
          ((ContinuousMap.precomp ρ).comp f₁) =
          (ContinuousMap.eval (ρ k) : C(∀ j, X j, X (ρ k))).comp f₁ from
        ContinuousMap.ext (fun _ => rfl)) =
      piEquiv f₀ f₁ S H (ρ k) := by
  apply HomotopyWith.ext
  intro st
  simp only [cast_apply, piEquiv_apply_apply, compContinuousMap_apply]
  rfl

end HomotopyRel

/-- Maps into a dependent product are homotopic relative to a set exactly when
all their coordinate maps are homotopic relative to the same set. -/
theorem homotopicRel_pi_iff (f₀ f₁ : C(A, ∀ i, X i)) (S : Set A) :
    f₀.HomotopicRel f₁ S ↔
      ∀ i, ((ContinuousMap.eval i : C(∀ j, X j, X i)).comp f₀).HomotopicRel
        ((ContinuousMap.eval i : C(∀ j, X j, X i)).comp f₁) S := by
  constructor
  · rintro ⟨H⟩ i
    exact ⟨HomotopyRel.piEquiv f₀ f₁ S H i⟩
  · intro h
    classical
    exact ⟨(HomotopyRel.piEquiv f₀ f₁ S).symm (fun i => Classical.choice (h i))⟩

end PiNaturality

end ContinuousMap
