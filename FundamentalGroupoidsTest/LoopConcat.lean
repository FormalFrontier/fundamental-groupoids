/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Category.TopCat.Based.Loop

/-!
# Evaluation of concatenated loop families under pre- and postcomposition

Strict naturality moves parameter precomposition and an induced loop map inside
concatenation. The all-time application law and the loop-map evaluation API then
identify both halves of the resulting clock, without unfolding the construction.
-/

universe u

open CategoryTheory BasedTopCat unitInterval Set Function

example {Q P X Y : BasedTopCat.{u}} (c : Q ⟶ P)
    (a b : P ⟶ loopFunctor.obj X) (f : X ⟶ Y) (q : Q.right) (t : unitInterval) :
    Path.toContinuousMap (x := point Y) (y := point Y)
        ((c ≫ loopConcat a b ≫ loopFunctor.map f).right.hom q) t =
      if h : (t : ℝ) ≤ 1 / 2 then
        f.right.hom (Path.toContinuousMap (x := point X) (y := point X)
          (a.right.hom (c.right.hom q))
          ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩)
      else
        f.right.hom (Path.toContinuousMap (x := point X) (y := point X)
          (b.right.hom (c.right.hom q))
          ⟨2 * t - 1,
            two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩) := by
  calc
    _ = Path.toContinuousMap (x := point Y) (y := point Y)
        ((loopConcat ((c ≫ a) ≫ loopFunctor.map f)
          ((c ≫ b) ≫ loopFunctor.map f)).right.hom q) t := by
      apply congrArg
        (fun k : Q ⟶ loopFunctor.obj Y ↦
          Path.toContinuousMap (x := point Y) (y := point Y) (k.right.hom q) t)
      rw [← Category.assoc, comp_loopConcat, loopConcat_comp_loopFunctor_map]
    _ = _ := by
      rw [loopConcat_apply_apply]
      split_ifs
      · exact loopFunctor_map_apply_apply f (a.right.hom (c.right.hom q)) _
      · exact loopFunctor_map_apply_apply f (b.right.hom (c.right.hom q)) _
