/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence.Exact.Total
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence.Exact.Fiber
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence.Exact.Base

/-!
# Exactness of pointed homotopy-fiber sequences

The chain complex associated to a continuous based map is exact in every
positive degree in the pointed-set sense: the incoming range is the inverse
image of the chosen point under the outgoing differential. Its terminal
degree-zero term need not be the range of the incoming differential.

The statements use ordinary topological spaces, the compact-open homotopy fiber
and cubical homotopy groups. They do not identify this model with a kified
loop-space sequence. They assert neither a group structure on path components
nor commutativity of the fundamental group.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, Sections 5–6.
-/

@[expose] public section

namespace HomotopyGroup

/-- The pointed homotopy-fiber sequence is exact at every positive chain degree.
No surjectivity onto its terminal degree-zero term is asserted. -/
theorem homotopyFiberSequence_exact.{v, uE, uB}
    {E : Type uE} {B : Type uB} [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (n : ℕ) :
    let S := homotopyFiberSequence.{v} f b e₀ h
    Set.range (S.d (n + 2) (n + 1)).toFun =
      (S.d (n + 1) n).toFun ⁻¹' {(S.X n).point} := by
  dsimp only
  let k := n / 3
  have hdiv : n % 3 + 3 * k = n := Nat.mod_add_div n 3
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h₀ | h₁ | h₂
  · have hn : n = 3 * k := by omega
    rw [hn]
    exact homotopyFiberSequence_exact_total.{v} f b e₀ h k
  · have hn : n = 3 * k + 1 := by omega
    have hsrc : n + 2 = 3 * k + 3 := by omega
    have hmid : n + 1 = 3 * k + 2 := by omega
    rw [hsrc, hmid, hn]
    exact homotopyFiberSequence_exact_fiber.{v} f b e₀ h k
  · have hn : n = 3 * k + 2 := by omega
    have hsrc : n + 2 = 3 * k + 4 := by omega
    have hmid : n + 1 = 3 * k + 3 := by omega
    rw [hsrc, hmid, hn]
    exact homotopyFiberSequence_exact_base.{v} f b e₀ h k

end HomotopyGroup
