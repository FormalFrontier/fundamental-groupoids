/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Compactness.CompactlyGeneratedSpace
public import FundamentalGroupoids.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies, fixed fibers and path components under compactly generated refinement

A relative homotopy from a `UCompactlyGeneratedSpace.{u}` source lifts to the
CompHaus-test compactly generated topology on its target without changing its
values. The interval product of the source is `u`-compactly generated, so the
construction lifts the entire jointly continuous map, not just its time slices.
The endpoint maps are their existing `ContinuousMap.toCompactlyGenerated` lifts,
and the homotopy remains fixed on the same arbitrary subset of the source.

Postcomposition by `ContinuousMap.compactlyGeneratedCounit` recovers the original
relative homotopy and is inverse to this lift. Refinement also commutes with
postcomposition, using `ContinuousMap.compactlyGeneratedMap` between refined
targets. Consequently relative-homotopy existence is unchanged by refinement.

The probe, source and target universes are independent. There are no separation
or compact-generation assumptions on the target, and no local compactness or
countability assumptions on the source. All constructions use the existing
relative-homotopy structures and the stock product topology on the cylinder.

For the ordinary compact-open function space `C(A, X)`, fixed evaluation over a
closed singleton defines a closed fiber. The closed-subtype comparison gives a
homeomorphism from refinement of this ordinary fiber to the fiber in the refined
function space. This refines the topology on `C(A, X)`, not on `X`. Both directions
leave functions and their values unchanged. The outward comparison and the
forward comparison exist without closedness. Based precomposition and
postcomposition between these fibers commute with the comparisons and, at closed
poles, with the homeomorphisms. These constructions use separate continuity of
precomposition and postcomposition in the compact-open topology, with no local
compactness or compact-generation assumptions on the source or target.

Paths also lift with unchanged values and endpoints. The outward comparison,
its restriction to any subtype, and its restriction to a fixed-evaluation fiber
induce bijections on path components. These component results require no
closedness and do not assert compact generation or a homeomorphism for an
arbitrary subspace.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 5 §§1–2,
  pp. 39–40, for compact-Hausdorff tests and the continuous identity from the
  compactly generated topology. May's convention also includes weak
  Hausdorffness, which is not assumed here.
* Mathlib's compactly generated topology and source-test continuity API,
  due to Dagur Asgeirsson and Etienne Marion, and its relative homotopies,
  due to Shing Tak Lam and contributors.
* Mathlib's paths and path-component quotient API.
* Mathlib's compact-open topology and its fixed-evaluation, precomposition and
  postcomposition continuity API, due to Reid Barton and contributors.
-/

@[expose] public section

universe u v w z

open TopologicalSpace unitInterval

namespace ContinuousMap

variable {A : Type v} {X : Type w}
variable [tA : TopologicalSpace A] [tX : TopologicalSpace X]
variable [UCompactlyGeneratedSpace.{u} A]

namespace HomotopyRel

variable {f g : C(A, X)} {s : Set A}

/-- Lift a relative homotopy to the CompHaus-test compactly generated topology
without changing its jointly continuous function or its fixed subset. -/
def toCompactlyGenerated (H : HomotopyRel f g s) :
    @HomotopyRel A X tA (compactlyGenerated.{u} X)
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g) s :=
  @ContinuousMap.HomotopyWith.mk A X tA (compactlyGenerated.{u} X)
    (ContinuousMap.toCompactlyGenerated.{u} f)
    (ContinuousMap.toCompactlyGenerated.{u} g)
    (fun k ↦ ∀ a ∈ s, k a = (ContinuousMap.toCompactlyGenerated.{u} f) a)
    (@ContinuousMap.Homotopy.mk A X tA (compactlyGenerated.{u} X)
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g)
      (@ContinuousMap.toCompactlyGenerated.{u} (I × A) X
        inferInstance tX inferInstance H.toContinuousMap)
      (fun a ↦ H.apply_zero a)
      (fun a ↦ H.apply_one a))
    (fun t a ha ↦ H.eq_fst t (x := a) ha)

/-- The lifted relative homotopy has the same values on the whole cylinder. -/
@[simp]
theorem toCompactlyGenerated_apply (H : HomotopyRel f g s) (p : I × A) :
    toCompactlyGenerated.{u} H p = H p :=
  rfl

/-- The underlying continuous map is the lift of the joint continuous map. -/
@[simp]
theorem toCompactlyGenerated_toContinuousMap (H : HomotopyRel f g s) :
    @_root_.toContinuousMap
      (@HomotopyRel A X tA (compactlyGenerated.{u} X)
        (ContinuousMap.toCompactlyGenerated.{u} f)
        (ContinuousMap.toCompactlyGenerated.{u} g) s)
      (I × A) X inferInstance (compactlyGenerated.{u} X)
      inferInstance inferInstance (toCompactlyGenerated.{u} H) =
      @ContinuousMap.toCompactlyGenerated.{u} (I × A) X
        inferInstance tX inferInstance H.toContinuousMap :=
  rfl

/-- Postcomposing a lifted relative homotopy with the outward comparison
recovers the original relative homotopy. -/
@[simp]
theorem compactlyGeneratedCounit_comp_toCompactlyGenerated (H : HomotopyRel f g s) :
    @HomotopyRel.compContinuousMap A X X tA (compactlyGenerated.{u} X) tX s
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g) (toCompactlyGenerated.{u} H)
      (ContinuousMap.compactlyGeneratedCounit.{u} X) = H := by
  apply @ContinuousMap.HomotopyWith.ext A X tA tX
  intro p
  rfl

/-- Lifting the outward composite recovers a relative homotopy into the
compactly generated topology. -/
@[simp]
theorem toCompactlyGenerated_comp_compactlyGeneratedCounit
    {p q : @ContinuousMap A X tA (compactlyGenerated.{u} X)}
    (H : @HomotopyRel A X tA (compactlyGenerated.{u} X) p q s) :
    toCompactlyGenerated.{u}
      (@HomotopyRel.compContinuousMap A X X tA (compactlyGenerated.{u} X) tX s p q H
        (ContinuousMap.compactlyGeneratedCounit.{u} X)) = H := by
  apply @ContinuousMap.HomotopyWith.ext A X tA (compactlyGenerated.{u} X)
  intro r
  rfl

/-- Refining a relative homotopy commutes with target postcomposition. -/
theorem toCompactlyGenerated_compContinuousMap
    {Y : Type z} [tY : TopologicalSpace Y]
    (H : HomotopyRel f g s) (h : C(X, Y)) :
    toCompactlyGenerated.{u}
      (@HomotopyRel.compContinuousMap A X Y tA tX tY s f g H h) =
      @HomotopyRel.compContinuousMap A X Y tA (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y) s
        (ContinuousMap.toCompactlyGenerated.{u} f)
        (ContinuousMap.toCompactlyGenerated.{u} g) (toCompactlyGenerated.{u} H)
        (ContinuousMap.compactlyGeneratedMap.{u} h) := by
  apply @ContinuousMap.HomotopyWith.ext A Y tA (compactlyGenerated.{u} Y)
  intro p
  rfl

end HomotopyRel

/-- Relative homotopies between the lifted endpoint maps exist exactly when
relative homotopies between the original maps exist, with the same fixed subset. -/
theorem homotopicRel_toCompactlyGenerated_iff (f g : C(A, X)) (s : Set A) :
    @ContinuousMap.HomotopicRel A X tA (compactlyGenerated.{u} X)
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g) s ↔ HomotopicRel f g s := by
  constructor
  · intro h
    exact h.map (fun H ↦
      @HomotopyRel.compContinuousMap A X X tA (compactlyGenerated.{u} X) tX s
        (ContinuousMap.toCompactlyGenerated.{u} f)
        (ContinuousMap.toCompactlyGenerated.{u} g) H (compactlyGeneratedCounit.{u} X))
  · intro h
    exact h.map (fun H ↦ HomotopyRel.toCompactlyGenerated.{u} H)

end ContinuousMap

universe t

namespace ContinuousMap

section EvaluationFiber

variable {A : Type v} {X : Type w}
variable [tA : TopologicalSpace A] [tX : TopologicalSpace X]
variable (a : A) (x : X)

local notation "M" => C(A, X)
local notation "P" => {F : M // F a = x}
local notation "tM" => (@ContinuousMap.compactOpen A X tA tX)
local notation "tP" =>
  (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x) tM)

/-- Fixed evaluation over a closed singleton is closed in the ordinary
compact-open function space, without a local compactness hypothesis. -/
theorem isClosed_evalFiber (hx : IsClosed ({x} : Set X)) :
    IsClosed {F : M | F a = x} := by
  change IsClosed ((fun F : M ↦ F a) ⁻¹' ({x} : Set X))
  exact hx.preimage (continuous_eval_const a)

/-- The unchanged-function map from refinement of an ordinary evaluation fiber
to the fiber in the refined function space. No closedness hypothesis is needed. -/
def compactlyGeneratedEvalFiberComparison :
    @ContinuousMap P
      {F : M // ((@ContinuousMap.toFun M M
        (@compactlyGenerated.{u} M tM) tM
        (@compactlyGeneratedCounit.{u} M tM)) F) a = x}
      (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M
        (fun F : M ↦ ((@ContinuousMap.toFun M M
          (@compactlyGenerated.{u} M tM) tM
          (@compactlyGeneratedCounit.{u} M tM)) F) a = x)
        (@compactlyGenerated.{u} M tM)) :=
  compactlyGeneratedSubtypeComparison.{u} {F : M | F a = x}

/-- Restrict the outward function-space comparison to an evaluation fiber.
The codomain has its ordinary compact-open subtype topology. -/
def compactlyGeneratedEvalFiberCounit :
    @ContinuousMap
      {F : M // ((@ContinuousMap.toFun M M
        (@compactlyGenerated.{u} M tM) tM
        (@compactlyGeneratedCounit.{u} M tM)) F) a = x} P
      (@instTopologicalSpaceSubtype M
        (fun F : M ↦ ((@ContinuousMap.toFun M M
          (@compactlyGenerated.{u} M tM) tM
          (@compactlyGeneratedCounit.{u} M tM)) F) a = x)
        (@compactlyGenerated.{u} M tM)) tP :=
  compactlyGeneratedSubtypeCounit.{u} {F : M | F a = x}

/-- The forward comparison preserves the entire fiber point. -/
@[simp]
theorem compactlyGeneratedEvalFiberComparison_apply (F : P) :
    @ContinuousMap.toFun P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (compactlyGeneratedEvalFiberComparison.{u} a x) F = F :=
  rfl

/-- The forward comparison preserves every value of the underlying function. -/
theorem compactlyGeneratedEvalFiberComparison_eval (F : P) (b : A) :
    (@ContinuousMap.toFun P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (compactlyGeneratedEvalFiberComparison.{u} a x) F).val b = F.val b := by
  rw [compactlyGeneratedEvalFiberComparison_apply]

/-- The forward comparison still takes the prescribed value at the pole. -/
theorem compactlyGeneratedEvalFiberComparison_pole (F : P) :
    (@ContinuousMap.toFun P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (compactlyGeneratedEvalFiberComparison.{u} a x) F).val a = x := by
  rw [compactlyGeneratedEvalFiberComparison_eval]
  exact F.property

/-- The restricted outward comparison preserves the entire fiber point. -/
@[simp]
theorem compactlyGeneratedEvalFiberCounit_apply (F : P) :
    @ContinuousMap.toFun P P
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) tP
      (compactlyGeneratedEvalFiberCounit.{u} a x) F = F :=
  rfl

/-- The restricted outward comparison preserves every function value. -/
theorem compactlyGeneratedEvalFiberCounit_eval (F : P) (b : A) :
    (@ContinuousMap.toFun P P
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) tP
      (compactlyGeneratedEvalFiberCounit.{u} a x) F).val b = F.val b := by
  rw [compactlyGeneratedEvalFiberCounit_apply]

/-- The restricted outward comparison preserves the value at the pole. -/
theorem compactlyGeneratedEvalFiberCounit_pole (F : P) :
    (@ContinuousMap.toFun P P
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) tP
      (compactlyGeneratedEvalFiberCounit.{u} a x) F).val a = x := by
  rw [compactlyGeneratedEvalFiberCounit_eval]
  exact F.property

/-- The two fiber comparisons compose to the outward comparison for the
ordinary fiber. This triangle does not require a closed pole. -/
@[simp]
theorem compactlyGeneratedEvalFiberCounit_comp_comparison :
    @ContinuousMap.comp P P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) tP
      (compactlyGeneratedEvalFiberCounit.{u} a x)
      (compactlyGeneratedEvalFiberComparison.{u} a x) =
        @compactlyGeneratedCounit.{u} P tP :=
  compactlyGeneratedSubtypeCounit_comp_comparison.{u} {F : M | F a = x}

section Precomposition

variable {A' : Type z} [tA' : TopologicalSpace A']
variable (a' : A') (f : C(A', A)) (hf : f a' = a)

local notation "M'" => C(A', X)
local notation "P'" => {F : M' // F a' = x}
local notation "tM'" => (@ContinuousMap.compactOpen A' X tA' tX)
local notation "tP'" =>
  (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x) tM')

/-- Based precomposition between ordinary compact-open evaluation fibers. -/
def evalFiberPrecomp : @ContinuousMap P P' tP tP' := by
  let g : C(M, M') := compRightContinuousMap X f
  have hg : ∀ F : P, (g F.val) a' = x := by
    intro F
    change F.val (f a') = x
    rw [hf]
    exact F.property
  exact ⟨fun F ↦ ⟨g F.val, hg F⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk hg⟩

/-- Based precomposition between fibers in refined function spaces. This
restricts refinement of the ordinary ambient precomposition map. -/
def compactlyGeneratedEvalFiberPrecomp :
    @ContinuousMap
      {F : M // ((@ContinuousMap.toFun M M
        (@compactlyGenerated.{u} M tM) tM
        (@compactlyGeneratedCounit.{u} M tM)) F) a = x}
      {F : M' // ((@ContinuousMap.toFun M' M'
        (@compactlyGenerated.{u} M' tM') tM'
        (@compactlyGeneratedCounit.{u} M' tM')) F) a' = x}
      (@instTopologicalSpaceSubtype M
        (fun F : M ↦ ((@ContinuousMap.toFun M M
          (@compactlyGenerated.{u} M tM) tM
          (@compactlyGeneratedCounit.{u} M tM)) F) a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype M'
        (fun F : M' ↦ ((@ContinuousMap.toFun M' M'
          (@compactlyGenerated.{u} M' tM') tM'
          (@compactlyGeneratedCounit.{u} M' tM')) F) a' = x)
        (@compactlyGenerated.{u} M' tM')) := by
  let g : C(M, M') := compRightContinuousMap X f
  have hg : ∀ F ∈ {F : M | F a = x}, g F ∈ {F : M' | F a' = x} := by
    intro F hF
    change F (f a') = x
    rw [hf]
    exact hF
  let gκ := @compactlyGeneratedMap.{u} M M' tM tM' g
  letI : TopologicalSpace M := @compactlyGenerated.{u} M tM
  letI : TopologicalSpace M' := @compactlyGenerated.{u} M' tM'
  let k := gκ.restrict {F : M | ((@ContinuousMap.toFun M M
    (@compactlyGenerated.{u} M tM) tM
    (@compactlyGeneratedCounit.{u} M tM)) F) a = x}
  have hk : ∀ F, ((@ContinuousMap.toFun M' M'
    (@compactlyGenerated.{u} M' tM') tM'
    (@compactlyGeneratedCounit.{u} M' tM')) (k F)) a' = x :=
    fun F ↦ hg F.val F.property
  exact ⟨fun F ↦ ⟨k F, hk F⟩, k.continuous.subtype_mk hk⟩

/-- The underlying map of based precomposition is composition of functions. -/
@[simp]
theorem evalFiberPrecomp_apply (F : P) :
    (evalFiberPrecomp a x a' f hf F).val = F.val.comp f :=
  rfl

/-- Based precomposition computes by evaluation after the based source map. -/
theorem evalFiberPrecomp_eval (F : P) (b : A') :
    (evalFiberPrecomp a x a' f hf F).val b = F.val (f b) := by
  rw [evalFiberPrecomp_apply]
  rfl

/-- Based precomposition preserves the prescribed value at the pole. -/
theorem evalFiberPrecomp_pole (F : P) :
    (evalFiberPrecomp a x a' f hf F).val a' = x :=
  (evalFiberPrecomp a x a' f hf F).property

/-- Refined based precomposition has the same underlying continuous function. -/
@[simp]
theorem compactlyGeneratedEvalFiberPrecomp_apply (F : P) :
    (@DFunLike.coe
      (@ContinuousMap P P'
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM))
        (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
          (@compactlyGenerated.{u} M' tM')))
      P (fun _ ↦ P') inferInstance
      (compactlyGeneratedEvalFiberPrecomp.{u} a x a' f hf) F).val = F.val.comp f :=
  rfl

/-- Refined based precomposition has the expected pointwise values. -/
theorem compactlyGeneratedEvalFiberPrecomp_eval (F : P) (b : A') :
    (@ContinuousMap.toFun P P'
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
        (@compactlyGenerated.{u} M' tM'))
      (compactlyGeneratedEvalFiberPrecomp.{u} a x a' f hf) F).val b = F.val (f b) :=
  rfl

/-- Refined based precomposition preserves the value at the pole. -/
theorem compactlyGeneratedEvalFiberPrecomp_pole (F : P) :
    (@ContinuousMap.toFun P P'
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
        (@compactlyGenerated.{u} M' tM'))
      (compactlyGeneratedEvalFiberPrecomp.{u} a x a' f hf) F).val a' = x := by
  rw [compactlyGeneratedEvalFiberPrecomp_eval, hf]
  exact F.property

/-- The restricted outward comparisons commute with based precomposition. -/
theorem compactlyGeneratedEvalFiberCounit_precomp :
    @ContinuousMap.comp P P' P'
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
        (@compactlyGenerated.{u} M' tM')) tP'
      (compactlyGeneratedEvalFiberCounit.{u} a' x)
      (compactlyGeneratedEvalFiberPrecomp.{u} a x a' f hf) =
    @ContinuousMap.comp P P P'
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) tP tP'
      (evalFiberPrecomp a x a' f hf) (compactlyGeneratedEvalFiberCounit.{u} a x) := by
  refine @ContinuousMap.ext P P'
    (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
      (@compactlyGenerated.{u} M tM)) tP' _ _ ?_
  intro F
  apply Subtype.ext
  rfl

/-- The forward fiber comparisons commute with based precomposition. -/
theorem compactlyGeneratedEvalFiberComparison_precomp :
    @ContinuousMap.comp P P P' (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
        (@compactlyGenerated.{u} M' tM'))
      (compactlyGeneratedEvalFiberPrecomp.{u} a x a' f hf)
      (compactlyGeneratedEvalFiberComparison.{u} a x) =
    @ContinuousMap.comp P P' P' (@compactlyGenerated.{u} P tP)
      (@compactlyGenerated.{u} P' tP')
      (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
        (@compactlyGenerated.{u} M' tM'))
      (compactlyGeneratedEvalFiberComparison.{u} a' x)
      (@compactlyGeneratedMap.{u} P P' tP tP' (evalFiberPrecomp a x a' f hf)) := by
  refine @ContinuousMap.ext P P' (@compactlyGenerated.{u} P tP)
    (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
      (@compactlyGenerated.{u} M' tM')) _ _ ?_
  intro F
  apply Subtype.ext
  rfl

end Precomposition

section Postcomposition

variable {Y : Type t} [tY : TopologicalSpace Y]
variable (y : Y) (g : C(X, Y)) (hg : g x = y)

local notation "N" => C(A, Y)
local notation "R" => {F : N // F a = y}
local notation "tN" => (@ContinuousMap.compactOpen A Y tA tY)
local notation "tR" =>
  (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y) tN)

/-- Based postcomposition between ordinary compact-open evaluation fibers. -/
def evalFiberPostcomp : @ContinuousMap P R tP tR := by
  let k : C(M, N) := ⟨fun F ↦ g.comp F, continuous_postcomp g⟩
  have hk : ∀ F : P, (k F.val) a = y := by
    intro F
    change g (F.val a) = y
    rw [F.property]
    exact hg
  exact ⟨fun F ↦ ⟨k F.val, hk F⟩,
    (k.continuous.comp continuous_subtype_val).subtype_mk hk⟩

/-- Based postcomposition between fibers in refined function spaces. This
restricts refinement of the ordinary ambient postcomposition map. -/
def compactlyGeneratedEvalFiberPostcomp :
    @ContinuousMap
      {F : M // ((@ContinuousMap.toFun M M
        (@compactlyGenerated.{u} M tM) tM
        (@compactlyGeneratedCounit.{u} M tM)) F) a = x}
      {F : N // ((@ContinuousMap.toFun N N
        (@compactlyGenerated.{u} N tN) tN
        (@compactlyGeneratedCounit.{u} N tN)) F) a = y}
      (@instTopologicalSpaceSubtype M
        (fun F : M ↦ ((@ContinuousMap.toFun M M
          (@compactlyGenerated.{u} M tM) tM
          (@compactlyGeneratedCounit.{u} M tM)) F) a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype N
        (fun F : N ↦ ((@ContinuousMap.toFun N N
          (@compactlyGenerated.{u} N tN) tN
          (@compactlyGeneratedCounit.{u} N tN)) F) a = y)
        (@compactlyGenerated.{u} N tN)) := by
  let k : C(M, N) := ⟨fun F ↦ g.comp F, continuous_postcomp g⟩
  have hk : ∀ F ∈ {F : M | F a = x}, k F ∈ {F : N | F a = y} := by
    intro F hF
    change g (F a) = y
    rw [hF]
    exact hg
  let kκ := @compactlyGeneratedMap.{u} M N tM tN k
  letI : TopologicalSpace M := @compactlyGenerated.{u} M tM
  letI : TopologicalSpace N := @compactlyGenerated.{u} N tN
  let l := kκ.restrict {F : M | ((@ContinuousMap.toFun M M
    (@compactlyGenerated.{u} M tM) tM
    (@compactlyGeneratedCounit.{u} M tM)) F) a = x}
  have hl : ∀ F, ((@ContinuousMap.toFun N N
    (@compactlyGenerated.{u} N tN) tN
    (@compactlyGeneratedCounit.{u} N tN)) (l F)) a = y :=
    fun F ↦ hk F.val F.property
  exact ⟨fun F ↦ ⟨l F, hl F⟩, l.continuous.subtype_mk hl⟩

/-- The underlying map of based postcomposition is composition of functions. -/
@[simp]
theorem evalFiberPostcomp_apply (F : P) :
    (evalFiberPostcomp a x y g hg F).val = g.comp F.val :=
  rfl

/-- Based postcomposition computes by applying the based target map. -/
theorem evalFiberPostcomp_eval (F : P) (b : A) :
    (evalFiberPostcomp a x y g hg F).val b = g (F.val b) := by
  rw [evalFiberPostcomp_apply]
  rfl

/-- Based postcomposition preserves the prescribed value at the pole. -/
theorem evalFiberPostcomp_pole (F : P) :
    (evalFiberPostcomp a x y g hg F).val a = y :=
  (evalFiberPostcomp a x y g hg F).property

/-- Refined based postcomposition has the same underlying continuous function. -/
@[simp]
theorem compactlyGeneratedEvalFiberPostcomp_apply (F : P) :
    (@DFunLike.coe
      (@ContinuousMap P R
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM))
        (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
          (@compactlyGenerated.{u} N tN)))
      P (fun _ ↦ R) inferInstance
      (compactlyGeneratedEvalFiberPostcomp.{u} a x y g hg) F).val = g.comp F.val :=
  rfl

/-- Refined based postcomposition has the expected pointwise values. -/
theorem compactlyGeneratedEvalFiberPostcomp_eval (F : P) (b : A) :
    (@ContinuousMap.toFun P R
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
        (@compactlyGenerated.{u} N tN))
      (compactlyGeneratedEvalFiberPostcomp.{u} a x y g hg) F).val b = g (F.val b) :=
  rfl

/-- Refined based postcomposition preserves the value at the pole. -/
theorem compactlyGeneratedEvalFiberPostcomp_pole (F : P) :
    (@ContinuousMap.toFun P R
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
        (@compactlyGenerated.{u} N tN))
      (compactlyGeneratedEvalFiberPostcomp.{u} a x y g hg) F).val a = y := by
  rw [compactlyGeneratedEvalFiberPostcomp_eval, F.property]
  exact hg

/-- The restricted outward comparisons commute with based postcomposition. -/
theorem compactlyGeneratedEvalFiberCounit_postcomp :
    @ContinuousMap.comp P R R
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
        (@compactlyGenerated.{u} N tN)) tR
      (compactlyGeneratedEvalFiberCounit.{u} a y)
      (compactlyGeneratedEvalFiberPostcomp.{u} a x y g hg) =
    @ContinuousMap.comp P P R
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) tP tR
      (evalFiberPostcomp a x y g hg) (compactlyGeneratedEvalFiberCounit.{u} a x) := by
  refine @ContinuousMap.ext P R
    (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
      (@compactlyGenerated.{u} M tM)) tR _ _ ?_
  intro F
  apply Subtype.ext
  rfl

/-- The forward fiber comparisons commute with based postcomposition. -/
theorem compactlyGeneratedEvalFiberComparison_postcomp :
    @ContinuousMap.comp P P R (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
        (@compactlyGenerated.{u} N tN))
      (compactlyGeneratedEvalFiberPostcomp.{u} a x y g hg)
      (compactlyGeneratedEvalFiberComparison.{u} a x) =
    @ContinuousMap.comp P R R (@compactlyGenerated.{u} P tP)
      (@compactlyGenerated.{u} R tR)
      (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
        (@compactlyGenerated.{u} N tN))
      (compactlyGeneratedEvalFiberComparison.{u} a y)
      (@compactlyGeneratedMap.{u} P R tP tR (evalFiberPostcomp a x y g hg)) := by
  refine @ContinuousMap.ext P R (@compactlyGenerated.{u} P tP)
    (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
      (@compactlyGenerated.{u} N tN)) _ _ ?_
  intro F
  apply Subtype.ext
  rfl

end Postcomposition
end EvaluationFiber
end ContinuousMap

namespace Homeomorph

section EvaluationFiber

variable {A : Type v} {X : Type w}
variable [tA : TopologicalSpace A] [tX : TopologicalSpace X]
variable (a : A) (x : X)

local notation "M" => C(A, X)
local notation "P" => {F : M // F a = x}
local notation "tM" => (@ContinuousMap.compactOpen A X tA tX)
local notation "tP" =>
  (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x) tM)

/-- At a closed pole, refinement of the ordinary compact-open evaluation fiber
is homeomorphic to the fiber in the refined function space. Both directions
preserve the underlying continuous function. This refines the function-space
topology, not the topology on the codomain. -/
def compactlyGeneratedEvalFiber (hx : IsClosed ({x} : Set X)) :
    @Homeomorph P
      {F : M // ((@ContinuousMap.toFun M M
        (@compactlyGenerated.{u} M tM) tM
        (@ContinuousMap.compactlyGeneratedCounit.{u} M tM)) F) a = x}
      (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M
        (fun F : M ↦ ((@ContinuousMap.toFun M M
          (@compactlyGenerated.{u} M tM) tM
          (@ContinuousMap.compactlyGeneratedCounit.{u} M tM)) F) a = x)
        (@compactlyGenerated.{u} M tM)) :=
  compactlyGeneratedSubtype.{u} {F : M | F a = x}
    (ContinuousMap.isClosed_evalFiber a x hx)

/-- The evaluation-fiber homeomorphism leaves fiber points unchanged. -/
@[simp]
theorem compactlyGeneratedEvalFiber_apply (hx : IsClosed ({x} : Set X)) (F : P) :
    (@Homeomorph.toEquiv P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (compactlyGeneratedEvalFiber.{u} a x hx)) F = F :=
  rfl

/-- The inverse evaluation-fiber homeomorphism leaves fiber points unchanged. -/
@[simp]
theorem compactlyGeneratedEvalFiber_symm_apply (hx : IsClosed ({x} : Set X)) (F : P) :
    (@Homeomorph.toEquiv P P
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) (@compactlyGenerated.{u} P tP)
      (@Homeomorph.symm P P (@compactlyGenerated.{u} P tP)
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM))
        (compactlyGeneratedEvalFiber.{u} a x hx))) F = F :=
  rfl

/-- The homeomorphism preserves every value of its underlying function. -/
theorem compactlyGeneratedEvalFiber_eval (hx : IsClosed ({x} : Set X))
    (F : P) (b : A) :
    ((@Homeomorph.toEquiv P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (compactlyGeneratedEvalFiber.{u} a x hx)) F).val b = F.val b := by
  rw [compactlyGeneratedEvalFiber_apply]

/-- The inverse homeomorphism preserves every value of its underlying function. -/
theorem compactlyGeneratedEvalFiber_symm_eval (hx : IsClosed ({x} : Set X))
    (F : P) (b : A) :
    ((@Homeomorph.toEquiv P P
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) (@compactlyGenerated.{u} P tP)
      (@Homeomorph.symm P P (@compactlyGenerated.{u} P tP)
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM))
        (compactlyGeneratedEvalFiber.{u} a x hx))) F).val b = F.val b := by
  rw [compactlyGeneratedEvalFiber_symm_apply]

/-- The continuous map of the homeomorphism is the forward fiber comparison. -/
@[simp]
theorem compactlyGeneratedEvalFiber_toContinuousMap (hx : IsClosed ({x} : Set X)) :
    @_root_.toContinuousMap
      (@Homeomorph P P (@compactlyGenerated.{u} P tP)
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM)))
      P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      inferInstance inferInstance (compactlyGeneratedEvalFiber.{u} a x hx) =
        ContinuousMap.compactlyGeneratedEvalFiberComparison.{u} a x := by
  refine @ContinuousMap.ext P P (@compactlyGenerated.{u} P tP)
    (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
      (@compactlyGenerated.{u} M tM)) _ _ ?_
  intro F
  exact compactlyGeneratedEvalFiber_apply.{u} a x hx F

/-- The evaluation-fiber homeomorphism commutes with the outward comparison. -/
theorem compactlyGeneratedEvalFiber_counit (hx : IsClosed ({x} : Set X)) :
    @ContinuousMap.comp P P P (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM)) tP
      (ContinuousMap.compactlyGeneratedEvalFiberCounit.{u} a x)
      (@_root_.toContinuousMap
        (@Homeomorph P P (@compactlyGenerated.{u} P tP)
          (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
            (@compactlyGenerated.{u} M tM)))
        P P (@compactlyGenerated.{u} P tP)
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM))
        inferInstance inferInstance (compactlyGeneratedEvalFiber.{u} a x hx)) =
      @ContinuousMap.compactlyGeneratedCounit.{u} P tP := by
  rw [compactlyGeneratedEvalFiber_toContinuousMap]
  exact ContinuousMap.compactlyGeneratedEvalFiberCounit_comp_comparison.{u} a x

section Precomposition

variable {A' : Type z} [tA' : TopologicalSpace A']
variable (a' : A') (f : C(A', A)) (hf : f a' = a)

local notation "M'" => C(A', X)
local notation "P'" => {F : M' // F a' = x}
local notation "tM'" => (@ContinuousMap.compactOpen A' X tA' tX)
local notation "tP'" =>
  (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x) tM')

/-- At a closed pole, the evaluation-fiber homeomorphisms are natural under
based precomposition, as an equality of continuous maps. -/
theorem compactlyGeneratedEvalFiber_precomp (hx : IsClosed ({x} : Set X)) :
    @ContinuousMap.comp P P P' (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
        (@compactlyGenerated.{u} M' tM'))
      (ContinuousMap.compactlyGeneratedEvalFiberPrecomp.{u} a x a' f hf)
      (@_root_.toContinuousMap
        (@Homeomorph P P (@compactlyGenerated.{u} P tP)
          (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
            (@compactlyGenerated.{u} M tM)))
        P P (@compactlyGenerated.{u} P tP)
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM))
        inferInstance inferInstance (compactlyGeneratedEvalFiber.{u} a x hx)) =
    @ContinuousMap.comp P P' P' (@compactlyGenerated.{u} P tP)
      (@compactlyGenerated.{u} P' tP')
      (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
        (@compactlyGenerated.{u} M' tM'))
      (@_root_.toContinuousMap
        (@Homeomorph P' P' (@compactlyGenerated.{u} P' tP')
          (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
            (@compactlyGenerated.{u} M' tM')))
        P' P' (@compactlyGenerated.{u} P' tP')
        (@instTopologicalSpaceSubtype M' (fun F : M' ↦ F a' = x)
          (@compactlyGenerated.{u} M' tM'))
        inferInstance inferInstance (compactlyGeneratedEvalFiber.{u} a' x hx))
      (@ContinuousMap.compactlyGeneratedMap.{u} P P' tP tP'
        (ContinuousMap.evalFiberPrecomp a x a' f hf)) := by
  simpa only [compactlyGeneratedEvalFiber_toContinuousMap] using
    ContinuousMap.compactlyGeneratedEvalFiberComparison_precomp.{u} a x a' f hf

end Precomposition

section Postcomposition

variable {Y : Type t} [tY : TopologicalSpace Y]
variable (y : Y) (g : C(X, Y)) (hg : g x = y)

local notation "N" => C(A, Y)
local notation "R" => {F : N // F a = y}
local notation "tN" => (@ContinuousMap.compactOpen A Y tA tY)
local notation "tR" =>
  (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y) tN)

/-- The evaluation-fiber homeomorphisms are natural under based
postcomposition when both pole singletons are closed. The based maps themselves
do not require either closedness hypothesis. -/
theorem compactlyGeneratedEvalFiber_postcomp
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y)) :
    @ContinuousMap.comp P P R (@compactlyGenerated.{u} P tP)
      (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
        (@compactlyGenerated.{u} M tM))
      (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
        (@compactlyGenerated.{u} N tN))
      (ContinuousMap.compactlyGeneratedEvalFiberPostcomp.{u} a x y g hg)
      (@_root_.toContinuousMap
        (@Homeomorph P P (@compactlyGenerated.{u} P tP)
          (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
            (@compactlyGenerated.{u} M tM)))
        P P (@compactlyGenerated.{u} P tP)
        (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x)
          (@compactlyGenerated.{u} M tM))
        inferInstance inferInstance (compactlyGeneratedEvalFiber.{u} a x hx)) =
    @ContinuousMap.comp P R R (@compactlyGenerated.{u} P tP)
      (@compactlyGenerated.{u} R tR)
      (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
        (@compactlyGenerated.{u} N tN))
      (@_root_.toContinuousMap
        (@Homeomorph R R (@compactlyGenerated.{u} R tR)
          (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
            (@compactlyGenerated.{u} N tN)))
        R R (@compactlyGenerated.{u} R tR)
        (@instTopologicalSpaceSubtype N (fun F : N ↦ F a = y)
          (@compactlyGenerated.{u} N tN))
        inferInstance inferInstance (compactlyGeneratedEvalFiber.{u} a y hy))
      (@ContinuousMap.compactlyGeneratedMap.{u} P R tP tR
        (ContinuousMap.evalFiberPostcomp a x y g hg)) := by
  simpa only [compactlyGeneratedEvalFiber_toContinuousMap] using
    ContinuousMap.compactlyGeneratedEvalFiberComparison_postcomp.{u} a x y g hg

end Postcomposition
end EvaluationFiber
end Homeomorph

namespace Path

variable {Y : Type v} [tY : TopologicalSpace Y]

/-- Lift a path to the CompHaus-test compactly generated topology, without
changing its values or endpoints. -/
def toCompactlyGenerated {x y : Y} (p : Path x y) :
    @Path Y (@compactlyGenerated.{u} Y tY) x y :=
  @Path.mk Y (@compactlyGenerated.{u} Y tY) x y
    (@ContinuousMap.toCompactlyGenerated.{u} I Y inferInstance tY inferInstance
      p.toContinuousMap)
    p.source p.target

/-- Lifting a path leaves every value unchanged. -/
@[simp]
theorem toCompactlyGenerated_apply {x y : Y} (p : Path x y) (t : I) :
    toCompactlyGenerated.{u} p t = p t :=
  rfl

/-- Lift a path in any subtype to the subtype of the refined ambient space.
The ambient interval path lifts without changing its values, so its original
subtype membership proofs still apply. No closedness assumption is needed. -/
def toCompactlyGeneratedSubtype {s : Set Y} {x y : s} (p : Path x y) :
    @Path s
      (@instTopologicalSpaceSubtype Y s (@compactlyGenerated.{u} Y tY)) x y := by
  let f : @ContinuousMap I Y inferInstance (@compactlyGenerated.{u} Y tY) :=
    @ContinuousMap.toCompactlyGenerated.{u} I Y inferInstance tY inferInstance
      ((ContinuousMap.subtypeVal s).comp p.toContinuousMap)
  exact @Path.mk s
    (@instTopologicalSpaceSubtype Y s (@compactlyGenerated.{u} Y tY)) x y
    (@ContinuousMap.mk I s inferInstance
      (@instTopologicalSpaceSubtype Y s (@compactlyGenerated.{u} Y tY))
      (fun t ↦ p t)
      (@Continuous.subtype_mk Y I (@compactlyGenerated.{u} Y tY) inferInstance s
        (fun t ↦ (p t).val)
        (@ContinuousMap.continuous_toFun I Y inferInstance
          (@compactlyGenerated.{u} Y tY) f)
        (fun t ↦ (p t).property)))
    p.source p.target

/-- Lifting a subtype path leaves its subtype values unchanged. -/
@[simp]
theorem toCompactlyGeneratedSubtype_apply {s : Set Y} {x y : s}
    (p : Path x y) (t : I) :
    toCompactlyGeneratedSubtype.{u} p t = p t :=
  rfl

end Path

namespace ZerothHomotopy

private theorem bijective_map_of_surjective_of_joined
    {B : Type v} {D : Type w} [TopologicalSpace B] [TopologicalSpace D]
    (f : C(B, D)) (hf : Function.Surjective f)
    (hjoined : ∀ {x y : B}, Joined (f x) (f y) → Joined x y) :
    Function.Bijective (map f) := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y hxy
    exact Quotient.sound (hjoined (Quotient.exact hxy))
  · exact Quotient.map_surjective _ hf

/-- The outward comparison from the CompHaus-test compactly generated topology
induces a bijection on path components of any space, including the empty space. -/
theorem bijective_map_compactlyGeneratedCounit (Y : Type v) [tY : TopologicalSpace Y] :
    Function.Bijective
      (@map Y Y (@compactlyGenerated.{u} Y tY) tY
        (ContinuousMap.compactlyGeneratedCounit.{u} Y)) := by
  refine @bijective_map_of_surjective_of_joined Y Y
    (@compactlyGenerated.{u} Y tY) tY
    (ContinuousMap.compactlyGeneratedCounit.{u} Y) ?_ ?_
  · intro y
    exact ⟨y, rfl⟩
  · intro x y h
    rcases h with ⟨p⟩
    exact ⟨Path.toCompactlyGenerated.{u} p⟩

/-- Restricting the outward comparison to any subset induces a bijection on
path components. Paths lift in the ambient space and retain their membership
in the subset; the subset need not be closed. -/
theorem bijective_map_compactlyGeneratedSubtypeCounit
    {Y : Type v} [tY : TopologicalSpace Y] (s : Set Y) :
    Function.Bijective
      (@map s s
        (@instTopologicalSpaceSubtype Y s (@compactlyGenerated.{u} Y tY))
        (@instTopologicalSpaceSubtype Y s tY)
        (ContinuousMap.compactlyGeneratedSubtypeCounit.{u} s)) := by
  refine @bijective_map_of_surjective_of_joined s s
    (@instTopologicalSpaceSubtype Y s (@compactlyGenerated.{u} Y tY))
    (@instTopologicalSpaceSubtype Y s tY)
    (ContinuousMap.compactlyGeneratedSubtypeCounit.{u} s) ?_ ?_
  · intro y
    exact ⟨y, rfl⟩
  · intro x y h
    rcases h with ⟨p⟩
    exact ⟨Path.toCompactlyGeneratedSubtype.{u} p⟩

section EvaluationFiber

variable {A : Type v} {X : Type w}
variable [tA : TopologicalSpace A] [tX : TopologicalSpace X]
variable (a : A) (x : X)

local notation "M" => C(A, X)
local notation "P" => {F : M // F a = x}
local notation "tM" => (@ContinuousMap.compactOpen A X tA tX)
local notation "tP" =>
  (@instTopologicalSpaceSubtype M (fun F : M ↦ F a = x) tM)

/-- The restricted outward comparison from a fixed-evaluation fiber in the
refined function space to the original compact-open evaluation fiber induces a
bijection on path components. No closedness assumption on the pole is needed. -/
theorem bijective_map_compactlyGeneratedEvalFiberCounit :
    Function.Bijective
      (@map
        {F : M // ((@ContinuousMap.toFun M M
          (@compactlyGenerated.{u} M tM) tM
          (@ContinuousMap.compactlyGeneratedCounit.{u} M tM)) F) a = x} P
        (@instTopologicalSpaceSubtype M
          (fun F : M ↦ ((@ContinuousMap.toFun M M
            (@compactlyGenerated.{u} M tM) tM
            (@ContinuousMap.compactlyGeneratedCounit.{u} M tM)) F) a = x)
          (@compactlyGenerated.{u} M tM)) tP
        (ContinuousMap.compactlyGeneratedEvalFiberCounit.{u} a x)) :=
  bijective_map_compactlyGeneratedSubtypeCounit.{u} {F : M | F a = x}

end EvaluationFiber

end ZerothHomotopy
