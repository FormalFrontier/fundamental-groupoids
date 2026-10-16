/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.CategoryTheory.Endomorphism.Conjugation
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.Fin.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Examples of conjugation transport

The single-object groupoid of the additive integers, written multiplicatively,
has distinct isomorphisms inducing the same conjugation transport. In contrast,
conjugating one transposition by another in the single-object groupoid of
permutations of `Fin 3` changes the endomorphism. These examples exhibit both
nontrivial commutative transport and the need for the commutativity hypothesis.
The latter calculation uses the bridge to group conjugation; the comparison
criteria then detect a noncommuting pair, a noncentral loop and failure of
commutativity in this model.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.SingleObj

private theorem intEnd_isMulCommutative :
    IsMulCommutative (End (SingleObj.star (Multiplicative ℤ))) :=
  (SingleObj.toEnd (Multiplicative ℤ)).surjective.isMulCommutative inferInstance

/-- The generator of the integer group is a nonidentity isomorphism whose
conjugation transport is the same as transport along the identity. -/
theorem int_generator_conj_eq_refl :
    let x := SingleObj.star (Multiplicative ℤ)
    let α : x ≅ x := (Groupoid.isoEquivHom x x).symm
      (SingleObj.toEnd (Multiplicative ℤ) (Multiplicative.ofAdd (1 : ℤ)))
    α.hom ≠ 𝟙 x ∧ α.conj = (Iso.refl x).conj := by
  dsimp only
  constructor
  · change Multiplicative.ofAdd (1 : ℤ) ≠ Multiplicative.ofAdd (0 : ℤ)
    decide
  · let := intEnd_isMulCommutative
    exact Iso.conj_eq_of_isMulCommutative _ _

/-- In the symmetric group on three letters, conjugation by the transposition
of `0` and `1` changes the transposition of `1` and `2`. -/
theorem perm_fin_three_swap_conj_ne :
    let x := SingleObj.star (Equiv.Perm (Fin 3))
    let α : x ≅ x := (Groupoid.isoEquivHom x x).symm
      (SingleObj.toEnd (Equiv.Perm (Fin 3)) (Equiv.swap 0 1))
    let f : End x := SingleObj.toEnd (Equiv.Perm (Fin 3)) (Equiv.swap 1 2)
    α.conj f ≠ f := by
  dsimp only
  rw [Iso.conj_eq_mulAut_conj]
  intro h
  have h0 : (Equiv.swap (0 : Fin 3) 1) 2 = (Equiv.swap (1 : Fin 3) 2) 0 := by
    simpa [MulAut.conj_apply, ← map_mul, ← map_inv] using
      congrArg (fun p : End (SingleObj.star (Equiv.Perm (Fin 3))) =>
        (SingleObj.toEnd (Equiv.Perm (Fin 3))).symm p 0) h
  exact (by decide : (Equiv.swap (0 : Fin 3) 1) 2 ≠ (Equiv.swap (1 : Fin 3) 2) 0) h0

/-- The transposition loop is not central, and its changed conjugate detects
noncommutativity of the canonical endomorphism monoid of the symmetric group. -/
private theorem perm_fin_three_swap_noncommuting_and_noncentral :
    let x := SingleObj.star (Equiv.Perm (Fin 3))
    let α : x ≅ x := (Groupoid.isoEquivHom x x).symm
      (SingleObj.toEnd (Equiv.Perm (Fin 3)) (Equiv.swap 0 1))
    let f : End x := SingleObj.toEnd (Equiv.Perm (Fin 3)) (Equiv.swap 1 2)
    ¬ Commute f (End.of α.hom) ∧
      End.of α.hom ∉ Set.center (End x) ∧ ¬ IsMulCommutative (End x) := by
  dsimp only
  let x := SingleObj.star (Equiv.Perm (Fin 3))
  let α : x ≅ x := (Groupoid.isoEquivHom x x).symm
    (SingleObj.toEnd (Equiv.Perm (Fin 3)) (Equiv.swap 0 1))
  let f : End x := SingleObj.toEnd (Equiv.Perm (Fin 3)) (Equiv.swap 1 2)
  have hchange : α.conj f ≠ (Iso.refl x).conj f := by
    simpa only [Iso.refl_conj] using perm_fin_three_swap_conj_ne
  have hn : α.conj ≠ (Iso.refl x).conj := fun h => hchange (congrArg (fun e => e f) h)
  refine ⟨?_, ?_, ?_⟩
  · simpa [α, x, f] using (Iso.conj_apply_eq_iff_commute α (Iso.refl x) f).not.mp hchange
  · simpa [α, x] using (Iso.conj_eq_iff_mem_center α (Iso.refl x)).not.mp hn
  · exact (Iso.forall_conj_eq_iff_isMulCommutative (Iso.refl x)).not.mp
      (fun h => hn (h α))

end CategoryTheory.SingleObj
