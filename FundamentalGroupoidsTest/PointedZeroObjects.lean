/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.CategoryTheory.Category.Pointed

/-!
# Zero objects in pointed types

The chosen categorical zero has a subsingleton carrier, whereas a pointed Boolean
type is not a zero object.
-/

open CategoryTheory.Limits
open scoped ZeroObject

universe u

example : Subsingleton (0 : Pointed.{u}) :=
  (Pointed.isZero_iff_subsingleton _).mp (isZero_zero Pointed.{u})

example : ¬ IsZero (Pointed.of false) := by
  intro h
  have hsub := (Pointed.isZero_iff_subsingleton _).mp h
  have heq : (false : Bool) = true := @Subsingleton.elim _ hsub false true
  cases heq
