/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Product
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Topology.Homotopy.Product

/-!
# Homotopy quotients of indexed products

`GenLoop.pi` assembles a family of generalized loops into a generalized loop in
the dependent product. `HomotopyGroup.piComparison` sends a boundary-relative
homotopy class to its coordinate classes using `HomotopyGroup.mapFun` and
continuous coordinate evaluation. `HomotopyGroup.piEquiv` bundles this comparison
as an equivalence for every cube-index type. For a nonempty cube index with
decidable equality, `HomotopyGroup.piMulEquiv` uses the existing coordinate
homomorphisms and the canonical homotopy-group structures.

The cube index, family index and coordinate spaces have independent universes.
The generalized-loop constructor and quotient comparison allow empty or infinite
indices, without connectedness, separation, local compactness or finiteness
assumptions. For an empty cube index the boundary is empty, so representatives
may take any value, not necessarily the supplied point; the quotient describes
path components. An empty family gives the terminal product.

These statements generalize May's binary product statement in finite degrees
to arbitrary families and cube indices in Mathlib's boundary-relative cubical
model. For infinite indices, `Cube.boundary` is the union of coordinate faces,
not the ambient topological frontier. No comparison with sphere-domain homotopy
groups or with products in May's category of weak Hausdorff k-spaces is supplied
here.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 9 §4, printed p. 67,
  for the binary product statement in finite degrees.
* Mathlib's generalized loops and homotopy groups by Roberto Alvarez,
  `ContinuousMap.pi`, `ContinuousMap.eval` and `ContinuousMap.piEquiv` in
  `Mathlib.Topology.ContinuousMap.Basic` by Nicolò Cavalleri, and
  `ContinuousMap.HomotopyRel.pi` in `Mathlib.Topology.Homotopy.Product` by
  Praneeth Kolichala provide the continuous-map and relative-homotopy support.
* Mathlib's `Setoid.piQuotientEquiv` in `Mathlib.Data.Setoid.Basic` by
  Amelia Livingston and Bryan Gin-ge Chen, `Quotient.congr`, and `MonoidHom.pi`
  in `Mathlib.Algebra.Group.Pi.Lemmas` by Simon Hudon and Patrick Massot provide
  the quotient and homomorphism support.
* The existing `FundamentalGroup.piMulEquiv` in
  `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Product` by
  Formal Frontier Agents supplies the degree-one product formalization, using
  Mathlib's fundamental groups by Mark Lavrentyev and product groupoids by
  Praneeth Kolichala. Based postcomposition is provided by
  `FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map`.
-/

@[expose] public section

noncomputable section

universe s u v w

namespace GenLoop

variable {N : Type s} {ι : Type u} {X : ι → Type v}
variable [∀ i, TopologicalSpace (X i)] {p : ∀ i, X i}

/-- Assemble generalized loops with a common cube index into a generalized loop
in the dependent product, using continuous-map assembly. -/
def pi (γ : ∀ i, GenLoop N (X i) (p i)) : GenLoop N (∀ i, X i) p :=
  ⟨ContinuousMap.pi (fun i => (γ i).1), by
    intro t ht
    funext i
    exact GenLoop.boundary (γ i) t ht⟩

/-- Evaluation of an assembled generalized loop at a cube point and coordinate. -/
@[simp]
theorem pi_apply (γ : ∀ i, GenLoop N (X i) (p i))
    (t : N → unitInterval) (i : ι) :
    pi γ t i = γ i t :=
  rfl

/-- Postcomposition of an assembled generalized loop by coordinate evaluation
recovers that coordinate loop. -/
@[simp]
theorem map_eval_pi (γ : ∀ i, GenLoop N (X i) (p i)) (i : ι) :
    GenLoop.map (ContinuousMap.eval i) rfl (pi γ) = γ i := by
  apply GenLoop.ext
  intro t
  rfl

private def piCarrierEquiv :
    (∀ i, GenLoop N (X i) (p i)) ≃ GenLoop N (∀ i, X i) p where
  toFun := pi
  invFun γ i := GenLoop.map (ContinuousMap.eval i) rfl γ
  left_inv γ := by
    funext i
    exact map_eval_pi γ i
  right_inv γ := by
    apply GenLoop.ext
    intro t
    funext i
    rfl

private theorem homotopic_pi_iff (γ δ : ∀ i, GenLoop N (X i) (p i)) :
    Homotopic (pi γ) (pi δ) ↔ ∀ i, Homotopic (γ i) (δ i) := by
  constructor
  · intro h i
    have hγ :
        GenLoop.map (N := N) (ContinuousMap.eval i) (x := p) (y := p i) rfl
            (pi γ) = γ i :=
      map_eval_pi (N := N) (p := p) γ i
    have hδ :
        GenLoop.map (N := N) (ContinuousMap.eval i) (x := p) (y := p i) rfl
            (pi δ) = δ i :=
      map_eval_pi (N := N) (p := p) δ i
    exact Eq.mp
      (congrArg₂
        (fun a b : GenLoop N (X i) (p i) =>
          Homotopic (N := N) (X := X i) (x := p i) a b) hγ hδ)
      (Homotopic.map (N := N) (ContinuousMap.eval i) (x := p) (y := p i) rfl h)
  · intro h
    exact ⟨ContinuousMap.HomotopyRel.pi (fun i => Classical.choice (h i))⟩

end GenLoop

namespace HomotopyGroup

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- The coordinate comparison on boundary-relative homotopy quotients, defined
by the existing maps induced by continuous coordinate evaluation. This function
is defined for every cube index, including an empty index. -/
def piComparison (N : Type s) (p : ∀ i, X i) :
    HomotopyGroup N (∀ i, X i) p → ∀ i, HomotopyGroup N (X i) (p i) :=
  fun q i => mapFun N (ContinuousMap.eval i) rfl q

/-- A coordinate of the product comparison is induced by evaluation. -/
@[simp]
theorem piComparison_apply (N : Type s) (p : ∀ i, X i)
    (q : HomotopyGroup N (∀ i, X i) p) (i : ι) :
    piComparison N p q i = mapFun N (ContinuousMap.eval i) rfl q :=
  rfl

/-- On a representative, the comparison takes the class of each coordinate
of the generalized loop. -/
theorem piComparison_apply_class (N : Type s) (p : ∀ i, X i)
    (γ : GenLoop N (∀ i, X i) p) (i : ι) :
    piComparison N p (⟦γ⟧ : HomotopyGroup N (∀ i, X i) p) i =
      (⟦GenLoop.map (ContinuousMap.eval i) rfl γ⟧ : HomotopyGroup N (X i) (p i)) :=
  rfl

/-- The comparison preserves the chosen constant class in every degree. -/
theorem piComparison_const (N : Type s) (p : ∀ i, X i) :
    piComparison N p (⟦GenLoop.const⟧ : HomotopyGroup N (∀ i, X i) p) =
      fun i => (⟦GenLoop.const⟧ : HomotopyGroup N (X i) (p i)) := by
  funext i
  exact mapFun_const N (ContinuousMap.eval i) rfl

/-- Coordinate evaluation is a bijection on the boundary-relative homotopy
quotients of an arbitrary dependent product, for every cube index.

This is the arbitrary-family, arbitrary-cube-index cubical extension of the
binary finite-degree product statement in May, *A Concise Course in Algebraic
Topology*, Chapter 9 §4, p. 67. It does not identify the cubical quotients with
sphere-domain homotopy groups or compare products with those in May's category
of spaces. -/
theorem bijective_piComparison (N : Type s) (p : ∀ i, X i) :
    Function.Bijective (piComparison N p) := by
  let assembly : (∀ i, HomotopyGroup N (X i) (p i)) ≃
      HomotopyGroup N (∀ i, X i) p :=
    (Setoid.piQuotientEquiv (fun i => GenLoop.Homotopic.setoid N (p i))).trans
      (Quotient.congr (GenLoop.piCarrierEquiv (N := N) (p := p)) (by
        intro γ δ
        exact (GenLoop.homotopic_pi_iff γ δ).symm))
  have hcomparison :
      (assembly.symm : HomotopyGroup N (∀ i, X i) p →
        ∀ i, HomotopyGroup N (X i) (p i)) = piComparison N p := by
    funext q
    refine Quotient.inductionOn
      (motive := fun q : HomotopyGroup N (∀ i, X i) p =>
        assembly.symm q = piComparison N p q) q ?_
    intro γ
    funext i
    rfl
  exact (congrArg
    (fun f : HomotopyGroup N (∀ i, X i) p → ∀ i, HomotopyGroup N (X i) (p i) =>
      Function.Bijective f) hcomparison).mp assembly.symm.bijective

/-- The homotopy quotient of a dependent product is equivalent to the product
of its coordinate homotopy quotients. Its forward function is `piComparison`,
with no nonemptiness or decidable-equality requirement on either index. -/
def piEquiv (N : Type s) (p : ∀ i, X i) :
    HomotopyGroup N (∀ i, X i) p ≃ ∀ i, HomotopyGroup N (X i) (p i) :=
  Equiv.ofBijective (piComparison N p) (bijective_piComparison N p)

/-- The underlying function of the product equivalence is the coordinate
comparison. -/
theorem coe_piEquiv (N : Type s) (p : ∀ i, X i) :
    (piEquiv N p : HomotopyGroup N (∀ i, X i) p →
      ∀ i, HomotopyGroup N (X i) (p i)) = piComparison N p :=
  rfl

/-- A coordinate of the product equivalence is induced by evaluation. -/
@[simp]
theorem piEquiv_apply (N : Type s) (p : ∀ i, X i)
    (q : HomotopyGroup N (∀ i, X i) p) (i : ι) :
    piEquiv N p q i = mapFun N (ContinuousMap.eval i) rfl q :=
  rfl

/-- On a representative, the product equivalence takes the class of each
coordinate of the generalized loop. -/
theorem piEquiv_apply_class (N : Type s) (p : ∀ i, X i)
    (γ : GenLoop N (∀ i, X i) p) (i : ι) :
    piEquiv N p (⟦γ⟧ : HomotopyGroup N (∀ i, X i) p) i =
      (⟦GenLoop.map (ContinuousMap.eval i) rfl γ⟧ : HomotopyGroup N (X i) (p i)) :=
  rfl

/-- The product equivalence preserves the chosen constant class in every degree. -/
theorem piEquiv_const (N : Type s) (p : ∀ i, X i) :
    piEquiv N p (⟦GenLoop.const⟧ : HomotopyGroup N (∀ i, X i) p) =
      fun i => (⟦GenLoop.const⟧ : HomotopyGroup N (X i) (p i)) :=
  piComparison_const N p

/-- Classes in a product agree whenever all their coordinate classes agree,
without any nonemptiness assumption on either index. -/
@[ext]
theorem pi_ext (N : Type s) (p : ∀ i, X i)
    {a b : HomotopyGroup N (∀ i, X i) p}
    (h : ∀ i, mapFun N (ContinuousMap.eval i) (x := p) (y := p i) rfl a =
      mapFun N (ContinuousMap.eval i) (x := p) (y := p i) rfl b) : a = b :=
  (bijective_piComparison N p).1 (funext h)

/-- The inverse product equivalence sends a family of representative classes
to the class of the assembled generalized loop. -/
@[simp]
theorem piEquiv_symm_class (N : Type s) (p : ∀ i, X i)
    (γ : ∀ i, GenLoop N (X i) (p i)) :
    (piEquiv N p).symm (fun i => (⟦γ i⟧ : HomotopyGroup N (X i) (p i))) =
      (⟦GenLoop.pi γ⟧ : HomotopyGroup N (∀ i, X i) p) := by
  apply (piEquiv N p).injective
  have hinverse :
      piEquiv N p
          ((piEquiv N p).symm (fun i => (⟦γ i⟧ : HomotopyGroup N (X i) (p i)))) =
        fun i => (⟦γ i⟧ : HomotopyGroup N (X i) (p i)) :=
    (piEquiv N p).apply_symm_apply _
  funext i
  have hcoordinate :
      piEquiv N p
          ((piEquiv N p).symm (fun j => (⟦γ j⟧ : HomotopyGroup N (X j) (p j)))) i =
        (⟦γ i⟧ : HomotopyGroup N (X i) (p i)) :=
    congrFun hinverse i
  have hmap :
      (⟦GenLoop.map (N := N) (ContinuousMap.eval i) (x := p) (y := p i) rfl
        (GenLoop.pi γ)⟧ : HomotopyGroup N (X i) (p i)) =
          (⟦γ i⟧ : HomotopyGroup N (X i) (p i)) :=
    congrArg
      (fun δ : GenLoop N (X i) (p i) =>
        (⟦δ⟧ : HomotopyGroup N (X i) (p i)))
      (GenLoop.map_eval_pi (N := N) (p := p) γ i)
  have hclass :
      piEquiv N p (⟦GenLoop.pi γ⟧ : HomotopyGroup N (∀ j, X j) p) i =
        (⟦GenLoop.map (N := N) (ContinuousMap.eval i) (x := p) (y := p i) rfl
          (GenLoop.pi γ)⟧ : HomotopyGroup N (X i) (p i)) :=
    piEquiv_apply_class N p (GenLoop.pi γ) i
  exact Eq.trans (α := HomotopyGroup N (X i) (p i)) hcoordinate
    (Eq.trans (α := HomotopyGroup N (X i) (p i)) hmap.symm hclass.symm)

/-- The product equivalence commutes with arbitrary based coordinate maps.
The target spaces may lie in a universe independent of the source spaces. -/
theorem piEquiv_naturality (N : Type s) {Y : ι → Type w}
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i))
    (p : ∀ i, X i) (q : ∀ i, Y i) (hf : ∀ i, f i (p i) = q i)
    (a : HomotopyGroup N (∀ i, X i) p) :
    piEquiv N q
        (mapFun N (ContinuousMap.piMap f) (x := p) (y := q) (funext hf) a) =
      fun i => mapFun N (f i) (x := p i) (y := q i) (hf i) (piEquiv N p a i) := by
  funext i
  simp only [piEquiv_apply]
  exact @Eq.trans (HomotopyGroup N (Y i) (q i))
    _ (mapFun N ((f i).comp (ContinuousMap.eval i))
      (x := p) (y := q i) (hf i) a) _
    (congrFun
      (mapFun_comp N (ContinuousMap.eval i) (x := p) (y := q) (z := q i) rfl
        (ContinuousMap.piMap f) (funext hf)) a).symm
    (congrFun
      (mapFun_comp N (f i) (x := p) (y := p i) (z := q i) (hf i)
        (ContinuousMap.eval i) rfl) a)

section Group

variable (N : Type s) [DecidableEq N] [Nonempty N]

/-- The multiplicative product equivalence, formed from the canonical
homomorphisms induced by coordinate evaluation. Only the hypotheses for the
existing positive homotopy-group structures are required. -/
def piMulEquiv (p : ∀ i, X i) :
    HomotopyGroup N (∀ i, X i) p ≃* ∀ i, HomotopyGroup N (X i) (p i) :=
  let coordinateMap :
      HomotopyGroup N (∀ i, X i) p →* ∀ i, HomotopyGroup N (X i) (p i) :=
    MonoidHom.pi (fun i =>
      map N (ContinuousMap.eval i) (x := p) (y := p i) rfl)
  MulEquiv.ofBijective coordinateMap (by
    have h :
        (coordinateMap :
          HomotopyGroup N (∀ i, X i) p → ∀ i, HomotopyGroup N (X i) (p i)) =
            piComparison N p := by
      funext q i
      exact congrFun
        (coe_map_eq_mapFun N (ContinuousMap.eval i) (x := p) (y := p i) rfl) q
    exact (congrArg
      (fun f : HomotopyGroup N (∀ i, X i) p → ∀ i, HomotopyGroup N (X i) (p i) =>
        Function.Bijective f) h).mpr (bijective_piComparison N p))

/-- The forward homomorphism is the product of the existing coordinate
homomorphisms. -/
theorem piMulEquiv_toMonoidHom (p : ∀ i, X i) :
    (piMulEquiv N p).toMonoidHom =
      MonoidHom.pi (fun i =>
        map N (ContinuousMap.eval i) (x := p) (y := p i) rfl) := by
  apply MonoidHom.ext
  intro q
  funext i
  rfl

/-- Forgetting multiplication gives the all-index product equivalence. -/
theorem piMulEquiv_toEquiv (p : ∀ i, X i) :
    (piMulEquiv N p).toEquiv = piEquiv N p := by
  apply Equiv.ext
  intro q
  funext i
  rfl

/-- The multiplicative equivalence has the same underlying function as the raw
coordinate comparison. -/
theorem coe_piMulEquiv (p : ∀ i, X i) :
    (piMulEquiv N p : HomotopyGroup N (∀ i, X i) p →
      ∀ i, HomotopyGroup N (X i) (p i)) = piComparison N p :=
  rfl

/-- A coordinate of the multiplicative product equivalence is the existing
homomorphism induced by evaluation. -/
@[simp]
theorem piMulEquiv_apply (p : ∀ i, X i)
    (q : HomotopyGroup N (∀ i, X i) p) (i : ι) :
    piMulEquiv N p q i =
      map N (ContinuousMap.eval i) (x := p) (y := p i) rfl q :=
  rfl

/-- On a representative, the multiplicative product equivalence takes the class
of each coordinate of the generalized loop. -/
theorem piMulEquiv_apply_class (p : ∀ i, X i)
    (γ : GenLoop N (∀ i, X i) p) (i : ι) :
    piMulEquiv N p (⟦γ⟧ : HomotopyGroup N (∀ i, X i) p) i =
      (⟦GenLoop.map (ContinuousMap.eval i) rfl γ⟧ : HomotopyGroup N (X i) (p i)) :=
  rfl

/-- The inverse multiplicative equivalence has the same underlying function
as the all-index product equivalence. In particular its representative assembly
law is `piEquiv_symm_class`. -/
@[simp]
theorem piMulEquiv_symm_apply (p : ∀ i, X i)
    (q : ∀ i, HomotopyGroup N (X i) (p i)) :
    (piMulEquiv N p).symm q = (piEquiv N p).symm q := by
  exact congrArg
    (fun e : HomotopyGroup N (∀ i, X i) p ≃
      ∀ i, HomotopyGroup N (X i) (p i) => e.symm q)
    (piMulEquiv_toEquiv N p)

/-- The multiplicative product equivalence commutes with arbitrary based
coordinate maps, using the canonical homotopy-group structures. -/
theorem piMulEquiv_naturality {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) (p : ∀ i, X i) (q : ∀ i, Y i)
    (hf : ∀ i, f i (p i) = q i) (a : HomotopyGroup N (∀ i, X i) p) :
    piMulEquiv N q
        (map N (ContinuousMap.piMap f) (x := p) (y := q) (funext hf) a) =
      fun i => map N (f i) (x := p i) (y := q i) (hf i) (piMulEquiv N p a i) := by
  simpa only [coe_piEquiv, coe_piMulEquiv, coe_map_eq_mapFun] using
    (piEquiv_naturality N f p q hf a)

end Group

/-- In degree one, the homotopy-group and fundamental-group product equivalences
commute with the existing comparison, retaining the same coordinate classes. -/
theorem pi1MulEquivFundamentalGroup_piMulEquiv (p : ∀ i, X i)
    (a : HomotopyGroup (Fin 1) (∀ i, X i) p) (i : ι) :
    pi1MulEquivFundamentalGroup (X := X i) (x := p i)
        (piMulEquiv (Fin 1) p a i) =
      FundamentalGroup.piMulEquiv p
        (pi1MulEquivFundamentalGroup (X := ∀ i, X i) (x := p) a) i := by
  have hmap :
      (map (Fin 1) (ContinuousMap.eval i) (x := p) (y := p i) rfl :
        HomotopyGroup (Fin 1) (∀ j, X j) p → HomotopyGroup (Fin 1) (X i) (p i)) =
          mapFun (Fin 1) (ContinuousMap.eval i) (x := p) (y := p i) rfl :=
    coe_map_eq_mapFun (Fin 1) (ContinuousMap.eval i) (x := p) (y := p i) rfl
  have hcoordinate :
      piMulEquiv (Fin 1) p a i =
        mapFun (Fin 1) (ContinuousMap.eval i) (x := p) (y := p i) rfl a :=
    Eq.trans (α := HomotopyGroup (Fin 1) (X i) (p i))
      (piMulEquiv_apply (Fin 1) p a i) (congrFun hmap a)
  have hcomparison :
      pi1MulEquivFundamentalGroup (X := X i) (x := p i)
          (mapFun (Fin 1) (ContinuousMap.eval i) (x := p) (y := p i) rfl a) =
        FundamentalGroup.mapOfEq (ContinuousMap.eval i) (x := p) (y := p i) rfl
          (pi1MulEquivFundamentalGroup (X := ∀ j, X j) (x := p) a) :=
    Eq.trans (α := FundamentalGroup (X i) (p i))
      (congrArg
        (fun q : HomotopyGroup (Fin 1) (X i) (p i) =>
          pi1MulEquivFundamentalGroup (X := X i) (x := p i) q)
        (congrFun hmap a).symm)
      (pi1MulEquivFundamentalGroup_map (ContinuousMap.eval i)
        (x := p) (y := p i) rfl a)
  have heval :
      FundamentalGroup.mapOfEq (ContinuousMap.eval i) (x := p) (y := p i) rfl =
        FundamentalGroup.map (ContinuousMap.eval i) p :=
    FundamentalGroup.mapOfEq_rfl (ContinuousMap.eval i) p
  have heval_apply :
      FundamentalGroup.mapOfEq (ContinuousMap.eval i) (x := p) (y := p i) rfl
          (pi1MulEquivFundamentalGroup (X := ∀ j, X j) (x := p) a) =
        FundamentalGroup.map (ContinuousMap.eval i) p
          (pi1MulEquivFundamentalGroup (X := ∀ j, X j) (x := p) a) :=
    congrArg
      (fun f : FundamentalGroup (∀ j, X j) p →* FundamentalGroup (X i) (p i) =>
        f (pi1MulEquivFundamentalGroup (X := ∀ j, X j) (x := p) a)) heval
  have hfundamental :
      FundamentalGroup.piMulEquiv p
          (pi1MulEquivFundamentalGroup (X := ∀ j, X j) (x := p) a) i =
        FundamentalGroup.map (ContinuousMap.eval i) p
          (pi1MulEquivFundamentalGroup (X := ∀ j, X j) (x := p) a) :=
    FundamentalGroup.piMulEquiv_apply p
      (pi1MulEquivFundamentalGroup (X := ∀ j, X j) (x := p) a) i
  exact Eq.trans (α := FundamentalGroup (X i) (p i))
    (congrArg
      (fun q : HomotopyGroup (Fin 1) (X i) (p i) =>
        pi1MulEquivFundamentalGroup (X := X i) (x := p i) q) hcoordinate)
    (Eq.trans (α := FundamentalGroup (X i) (p i)) hcomparison
      (Eq.trans (α := FundamentalGroup (X i) (p i)) heval_apply hfundamental.symm))

end HomotopyGroup
