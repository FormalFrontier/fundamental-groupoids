/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Conj

/-!
# Comparing conjugation by different isomorphisms

Mathlib's `CategoryTheory.Iso.conj` transports endomorphisms along an isomorphism.
For two isomorphisms `α β : X ≅ Y`, the two transports agree on `f : End X` precisely
when `f` commutes with the relative loop `α.hom ≫ β.inv`. Consequently the whole
transports agree precisely when this loop is central, and they agree whenever the
canonical endomorphism monoid of `X` is commutative.

If every morphism is invertible, equality of all transports with the transport
along a fixed `α : X ≅ Y` also implies commutativity of `End X`. The fixed
isomorphism makes this characterization nonvacuous even when objects in different
components are present. The invertibility hypothesis is essential for this
converse: a noncommutative monoid with no nonidentity units gives a single-object
category whose only automorphism is the identity.

For a loop isomorphism in a groupoid, categorical conjugation agrees with
`MulAut.conj` on the canonical endomorphism group. Thus these comparisons extend
the existing categorical and group-theoretic conjugation APIs without introducing
another transport construction.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 1, §3: independence
  of basepoint change when the fundamental group is abelian. The commutative
  transport theorem below generalizes this result to arbitrary categories.
* `Mathlib.CategoryTheory.Conj` and `Mathlib.CategoryTheory.Endomorphism` provide
  the conjugation construction and the canonical endomorphism monoid and group.
* `Mathlib.Algebra.Group.Center` and `Mathlib.Algebra.Group.End` provide the center
  and group-conjugation APIs used here.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- Two isomorphisms induce the same conjugate of an endomorphism exactly when
that endomorphism commutes with their relative loop at the source. -/
theorem conj_apply_eq_iff_commute (α β : X ≅ Y) (f : End X) :
    α.conj f = β.conj f ↔ Commute f (End.of (α.hom ≫ β.inv)) := by
  rw [commute_iff_eq, End.mul_def, End.mul_def]
  constructor
  · intro h
    have h' := congrArg (fun k : End Y => α.hom ≫ k ≫ β.inv) h
    simpa only [conj_apply, Category.assoc, hom_inv_id_assoc, hom_inv_id,
      Category.comp_id] using h'.symm
  · intro h
    have h' := congrArg (fun k : End X => α.inv ≫ k ≫ β.hom) h
    simpa only [conj_apply, Category.assoc, inv_hom_id_assoc, inv_hom_id,
      Category.comp_id] using h'.symm

/-- Two isomorphisms induce the same equivalence of endomorphism monoids exactly
when their relative loop at the source is central. -/
theorem conj_eq_iff_mem_center (α β : X ≅ Y) :
    α.conj = β.conj ↔ End.of (α.hom ≫ β.inv) ∈ Set.center (End X) := by
  rw [Semigroup.mem_center_iff]
  constructor
  · intro h f
    exact (conj_apply_eq_iff_commute α β f).mp (congrArg (fun e => e f) h)
  · intro h
    exact MulEquiv.ext fun f => (conj_apply_eq_iff_commute α β f).mpr (h f)

/-- Conjugation transport is independent of the chosen isomorphism when the
canonical source endomorphism monoid is commutative. This generalizes the abelian
fundamental-group basepoint-change result of May, Chapter 1, §3. -/
theorem conj_eq_of_isMulCommutative [IsMulCommutative (End X)] (α β : X ≅ Y) :
    α.conj = β.conj := by
  exact (conj_eq_iff_mem_center α β).mpr
    (Semigroup.mem_center_iff.mpr fun f => mul_comm' f _)

/-- If every morphism is invertible, independence of conjugation transport to a
fixed target characterizes commutativity of the source endomorphism group.
The explicit isomorphism `α` ensures that the family of transports is nonempty. -/
theorem forall_conj_eq_iff_isMulCommutative [IsGroupoid C] (α : X ≅ Y) :
    (∀ β : X ≅ Y, β.conj = α.conj) ↔ IsMulCommutative (End X) := by
  constructor
  · intro h
    apply isMulCommutative_iff.mpr
    intro f g
    -- Precomposing the fixed isomorphism by `g` realizes any desired relative loop.
    have hg := (conj_eq_iff_mem_center ((asIso g) ≪≫ α) α).mp (h _)
    have hg' : g ∈ Set.center (End X) := by simpa using hg
    exact (Semigroup.mem_center_iff.mp hg') f
  · intro h β
    let := h
    exact conj_eq_of_isMulCommutative β α

/-- Categorical conjugation by a loop isomorphism agrees with group conjugation
by its underlying element of the canonical endomorphism group. -/
theorem conj_eq_mulAut_conj {G : Type u} [Groupoid.{v} G] {x : G} (α : x ≅ x) :
    α.conj = MulAut.conj (End.of α.hom) := by
  have hinv : (End.of α.hom)⁻¹ = End.of α.inv :=
    inv_eq_of_mul_eq_one_right (show End.of α.hom * End.of α.inv = 1 from α.inv_hom_id)
  apply MulEquiv.ext
  intro f
  simp only [conj_apply, MulAut.conj_apply, hinv, End.mul_def]

end CategoryTheory.Iso
