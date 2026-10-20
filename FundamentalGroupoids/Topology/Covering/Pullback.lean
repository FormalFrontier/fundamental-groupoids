/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Components
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Data.Set.Prod

/-!
# Fibers and monodromy of pullback coverings

The carrier is `Function.Pullback f₁ f₂`, with its existing product/subtype topology.
Its map to the common base is `z ↦ f₁ z.fst`. The point fiber of this map is the product
of the two point fibers, and this identification intertwines the covering-space
monodromy, including transport along paths with different endpoints.

There are two covering statements: stability of a projection under continuous base change,
and the covering property of the map to the common base when both maps are coverings.
The latter uses simultaneous evenly covered neighborhoods and product charts, not closure
under arbitrary composition of covering maps.

The orbit comparison uses the canonical `fundamentalGroupMulAction` of the pullback
covering and the stock diagonal product action on the two fibers. The component comparison
composes this with the monodromy-orbit/path-component equivalence.

## References

* Mathlib's `Function.Pullback` and `Function.mapPullback` for the fiber product.
* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for monodromy and canonical actions.
* `FundamentalGroupoids.Topology.Covering.Monodromy` for naturality of monodromy.
* `FundamentalGroupoids.Topology.Covering.Components` for path-component comparison.
-/

@[expose] public section

universe u₁ u₂ v u₁' u₂' t

namespace Function.Pullback

variable {E₁ : Type u₁} {E₂ : Type u₂} {B : Type v}

/-- The point fiber of the map from a pullback to the common base is the product
of the original point fibers. The maps retain the original coordinates. -/
def fiberEquiv (f₁ : E₁ → B) (f₂ : E₂ → B) (b : B) :
    ((fun z : f₁.Pullback f₂ ↦ f₁ z.fst) ⁻¹' {b}) ≃
      (f₁ ⁻¹' {b}) × (f₂ ⁻¹' {b}) where
  toFun e := (⟨e.val.fst, e.property⟩,
    ⟨e.val.snd, e.val.property.symm.trans e.property⟩)
  invFun e := ⟨⟨(e.1.val, e.2.val), e.1.property.trans e.2.property.symm⟩,
    e.1.property⟩
  left_inv _ := Subtype.ext (Subtype.ext (Prod.ext rfl rfl))
  right_inv _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- The first coordinate is the first original total-space point. -/
@[simp] theorem fiberEquiv_apply_fst_val (f₁ : E₁ → B) (f₂ : E₂ → B) (b : B)
    (e : (fun z : f₁.Pullback f₂ ↦ f₁ z.fst) ⁻¹' {b}) :
    (fiberEquiv f₁ f₂ b e).1.val = e.val.fst := rfl

/-- The second coordinate is the second original total-space point. -/
@[simp] theorem fiberEquiv_apply_snd_val (f₁ : E₁ → B) (f₂ : E₂ → B) (b : B)
    (e : (fun z : f₁.Pullback f₂ ↦ f₁ z.fst) ⁻¹' {b}) :
    (fiberEquiv f₁ f₂ b e).2.val = e.val.snd := rfl

/-- The inverse pairs the two original total-space points. -/
@[simp] theorem fiberEquiv_symm_apply_val (f₁ : E₁ → B) (f₂ : E₂ → B) (b : B)
    (e₁ : f₁ ⁻¹' {b}) (e₂ : f₂ ⁻¹' {b}) :
    ((fiberEquiv f₁ f₂ b).symm (e₁, e₂)).val.val = (e₁.val, e₂.val) := rfl

/-- The inverse fiber comparison commutes with the stock pullback map induced by two
maps over the same base. This is set-level naturality, without covering hypotheses. -/
theorem fiberEquiv_symm_mapPullback
    {E₁' : Type u₁'} {E₂' : Type u₂'}
    {f₁ : E₁ → B} {f₂ : E₂ → B} {f₁' : E₁' → B} {f₂' : E₂' → B}
    (a₁ : E₁ → E₁') (a₂ : E₂ → E₂')
    (ha₁ : f₁' ∘ a₁ = f₁) (ha₂ : f₂' ∘ a₂ = f₂)
    (b : B) (e₁ : f₁ ⁻¹' {b}) (e₂ : f₂ ⁻¹' {b}) :
    Function.mapPullback a₁ id a₂ ha₁ ha₂
        ((fiberEquiv f₁ f₂ b).symm (e₁, e₂)).val =
      ((fiberEquiv f₁' f₂' b).symm
        (⟨a₁ e₁.val, (congr_fun ha₁ e₁.val).trans e₁.property⟩,
         ⟨a₂ e₂.val, (congr_fun ha₂ e₂.val).trans e₂.property⟩)).val :=
  Subtype.ext rfl

end Function.Pullback

namespace IsCoveringMap

variable {E₁ : Type u₁} {E₂ : Type u₂} {B : Type v}
  [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace B]
  {f₁ : E₁ → B} {f₂ : E₂ → B}

/-- A covering remains a covering under continuous base change. Empty fibers are allowed. -/
theorem pullback_snd (cov₁ : IsCoveringMap f₁)
    {A : Type t} [TopologicalSpace A] (g : A → B) (hg : Continuous g) :
    IsCoveringMap (Function.Pullback.snd : f₁.Pullback g → A) := by
  intro a
  rcases cov₁ (g a) with ⟨hI, U, haU, hU, _, H, hH⟩
  let := hI
  let V : Set A := g ⁻¹' U
  let F := f₁ ⁻¹' {g a}
  let j : (Function.Pullback.snd : f₁.Pullback g → A) ⁻¹' V → f₁ ⁻¹' U :=
    fun z ↦ ⟨z.val.fst, by
      change f₁ z.val.fst ∈ U
      have hz : f₁ z.val.fst = g z.val.snd := z.val.property
      rw [hz]
      exact z.property⟩
  let k : V × F → U × F := fun ai ↦ (⟨g ai.1.val, ai.1.property⟩, ai.2)
  have hinv (ai : V × F) : f₁ (H.symm (k ai)).val = g ai.1.val := by
    simpa only [H.apply_symm_apply] using (hH (H.symm (k ai))).symm
  have hchart : IsEvenlyCovered (Function.Pullback.snd : f₁.Pullback g → A) a F := by
    refine ⟨inferInstance, V, haU, hU.preimage hg,
      (hU.preimage hg).preimage (continuous_snd.comp continuous_subtype_val), ?_⟩
    refine ⟨{
      toFun := fun z ↦ (⟨z.val.snd, z.property⟩, (H (j z)).2)
      invFun := fun ai ↦ ⟨⟨((H.symm (k ai)).val, ai.1.val), hinv ai⟩, ai.1.property⟩
      left_inv := fun z ↦ by
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · have hp : k (⟨z.val.snd, z.property⟩, (H (j z)).2) = H (j z) := by
            apply Prod.ext
            · apply Subtype.ext
              exact z.val.property.symm.trans (hH (j z)).symm
            · rfl
          exact congrArg Subtype.val ((congrArg H.symm hp).trans (H.symm_apply_apply (j z)))
        · rfl
      right_inv := fun ai ↦ by
        apply Prod.ext
        · exact Subtype.ext rfl
        · change (H (H.symm (k ai))).2 = ai.2
          exact congrArg (fun x : U × F ↦ x.2) (H.apply_symm_apply (k ai))
      continuous_toFun := by
        dsimp only [j, Function.Pullback.fst, Function.Pullback.snd]
        fun_prop
      continuous_invFun := by
        dsimp only [k]
        fun_prop }, fun _ ↦ rfl⟩
  exact hchart.to_isEvenlyCovered_preimage

/-- The map from a pullback of two coverings to their common base is a covering.
Simultaneous local charts, not arbitrary composition of coverings, give this property. -/
theorem pullback_base (cov₁ : IsCoveringMap f₁) (cov₂ : IsCoveringMap f₂) :
    IsCoveringMap (fun z : f₁.Pullback f₂ ↦ f₁ z.fst) := by
  intro b
  rcases cov₁ b with ⟨hI₁, U₁, hb₁, hU₁, _, H₁, hH₁⟩
  rcases cov₂ b with ⟨hI₂, U₂, hb₂, hU₂, _, H₂, hH₂⟩
  let := hI₁
  let := hI₂
  let U : Set B := U₁ ∩ U₂
  let F₁ := f₁ ⁻¹' {b}
  let F₂ := f₂ ⁻¹' {b}
  let p : f₁.Pullback f₂ → B := fun z ↦ f₁ z.fst
  let j₁ : p ⁻¹' U → f₁ ⁻¹' U₁ := fun z ↦ ⟨z.val.fst, z.property.1⟩
  let j₂ : p ⁻¹' U → f₂ ⁻¹' U₂ := fun z ↦ ⟨z.val.snd, by
    change f₂ z.val.snd ∈ U₂
    have hz : f₁ z.val.fst = f₂ z.val.snd := z.val.property
    rw [← hz]
    exact z.property.2⟩
  let k₁ : U × (F₁ × F₂) → U₁ × F₁ :=
    fun ui ↦ (⟨ui.1.val, ui.1.property.1⟩, ui.2.1)
  let k₂ : U × (F₁ × F₂) → U₂ × F₂ :=
    fun ui ↦ (⟨ui.1.val, ui.1.property.2⟩, ui.2.2)
  have hinv₁ (ui : U × (F₁ × F₂)) : f₁ (H₁.symm (k₁ ui)).val = ui.1.val := by
    simpa only [H₁.apply_symm_apply] using (hH₁ (H₁.symm (k₁ ui))).symm
  have hinv₂ (ui : U × (F₁ × F₂)) : f₂ (H₂.symm (k₂ ui)).val = ui.1.val := by
    simpa only [H₂.apply_symm_apply] using (hH₂ (H₂.symm (k₂ ui))).symm
  have hp : Continuous p := cov₁.continuous.comp (continuous_fst.comp continuous_subtype_val)
  have hchart : IsEvenlyCovered p b (F₁ × F₂) := by
    refine ⟨inferInstance, U, ⟨hb₁, hb₂⟩, hU₁.inter hU₂,
      (hU₁.inter hU₂).preimage hp, ?_⟩
    refine ⟨{
      toFun := fun z ↦ (⟨p z.val, z.property⟩, ((H₁ (j₁ z)).2, (H₂ (j₂ z)).2))
      invFun := fun ui ↦ ⟨⟨((H₁.symm (k₁ ui)).val, (H₂.symm (k₂ ui)).val),
        (hinv₁ ui).trans (hinv₂ ui).symm⟩, by
          change f₁ (H₁.symm (k₁ ui)).val ∈ U
          rw [hinv₁ ui]
          exact ui.1.property⟩
      left_inv := fun z ↦ by
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · have he : k₁ (⟨p z.val, z.property⟩,
              ((H₁ (j₁ z)).2, (H₂ (j₂ z)).2)) = H₁ (j₁ z) := by
            apply Prod.ext
            · exact Subtype.ext (hH₁ (j₁ z)).symm
            · rfl
          exact congrArg Subtype.val ((congrArg H₁.symm he).trans (H₁.symm_apply_apply (j₁ z)))
        · have he : k₂ (⟨p z.val, z.property⟩,
              ((H₁ (j₁ z)).2, (H₂ (j₂ z)).2)) = H₂ (j₂ z) := by
            apply Prod.ext
            · exact Subtype.ext (z.val.property.trans (hH₂ (j₂ z)).symm)
            · rfl
          exact congrArg Subtype.val ((congrArg H₂.symm he).trans (H₂.symm_apply_apply (j₂ z)))
      right_inv := fun ui ↦ by
        apply Prod.ext
        · exact Subtype.ext (hinv₁ ui)
        · apply Prod.ext
          · change (H₁ (H₁.symm (k₁ ui))).2 = ui.2.1
            exact congrArg (fun x : U₁ × F₁ ↦ x.2) (H₁.apply_symm_apply (k₁ ui))
          · change (H₂ (H₂.symm (k₂ ui))).2 = ui.2.2
            exact congrArg (fun x : U₂ × F₂ ↦ x.2) (H₂.apply_symm_apply (k₂ ui))
      continuous_toFun := by
        dsimp only [j₁, j₂, Function.Pullback.fst, Function.Pullback.snd]
        fun_prop
      continuous_invFun := by
        dsimp only [k₁, k₂]
        fun_prop }, fun _ ↦ rfl⟩
  exact hchart.to_isEvenlyCovered_preimage

/-- Projection of the lifted path to the first total space is its canonical lift. -/
theorem pullback_liftPath_fst (cov₁ : IsCoveringMap f₁) (cov₂ : IsCoveringMap f₂)
    (γ : C(unitInterval, B)) (z : f₁.Pullback f₂)
    (hγ : γ 0 = f₁ z.fst) (s : unitInterval) :
    ((cov₁.pullback_base cov₂).liftPath γ z hγ s).fst =
      cov₁.liftPath γ z.fst hγ s := by
  let Γ := (cov₁.pullback_base cov₂).liftPath γ z hγ
  have hΓ : (fun t ↦ (Γ t).fst) = cov₁.liftPath γ z.fst hγ :=
    (cov₁.eq_liftPath_iff hγ).2
      ⟨continuous_fst.comp (continuous_subtype_val.comp Γ.continuous),
        (cov₁.pullback_base cov₂).liftPath_lifts γ z hγ,
        congrArg Function.Pullback.fst ((cov₁.pullback_base cov₂).liftPath_zero γ z hγ)⟩
  exact congr_fun hΓ s

/-- Projection of the lifted path to the second total space is its canonical lift. -/
theorem pullback_liftPath_snd (cov₁ : IsCoveringMap f₁) (cov₂ : IsCoveringMap f₂)
    (γ : C(unitInterval, B)) (z : f₁.Pullback f₂)
    (hγ : γ 0 = f₁ z.fst) (s : unitInterval) :
    ((cov₁.pullback_base cov₂).liftPath γ z hγ s).snd =
      cov₂.liftPath γ z.snd (hγ.trans z.property) s := by
  let Γ := (cov₁.pullback_base cov₂).liftPath γ z hγ
  have hΓ : (fun t ↦ (Γ t).snd) =
      cov₂.liftPath γ z.snd (hγ.trans z.property) :=
    (cov₂.eq_liftPath_iff (hγ.trans z.property)).2
      ⟨continuous_snd.comp (continuous_subtype_val.comp Γ.continuous),
        funext fun t ↦ (Γ t).property.symm.trans
          (congr_fun ((cov₁.pullback_base cov₂).liftPath_lifts γ z hγ) t),
        congrArg Function.Pullback.snd ((cov₁.pullback_base cov₂).liftPath_zero γ z hγ)⟩
  exact congr_fun hΓ s

/-- The fiber comparison intertwines monodromy along every path class. -/
theorem pullbackFiberEquiv_monodromy
    (cov₁ : IsCoveringMap f₁) (cov₂ : IsCoveringMap f₂) {x y : B}
    (γ : Path.Homotopic.Quotient x y)
    (e : (fun z : f₁.Pullback f₂ ↦ f₁ z.fst) ⁻¹' {x}) :
    Function.Pullback.fiberEquiv f₁ f₂ y
        ((cov₁.pullback_base cov₂).monodromy γ e) =
      (cov₁.monodromy γ (Function.Pullback.fiberEquiv f₁ f₂ x e).1,
       cov₂.monodromy γ (Function.Pullback.fiberEquiv f₁ f₂ x e).2) := by
  let π₁ : C(f₁.Pullback f₂, E₁) :=
    ⟨Function.Pullback.fst, continuous_fst.comp continuous_subtype_val⟩
  let π₂ : C(f₁.Pullback f₂, E₂) :=
    ⟨Function.Pullback.snd, continuous_snd.comp continuous_subtype_val⟩
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg Subtype.val
      ((cov₁.pullback_base cov₂).monodromy_naturality cov₁ π₁ rfl γ e)).symm
  · apply Subtype.ext
    exact (congrArg Subtype.val
      ((cov₁.pullback_base cov₂).monodromy_naturality cov₂ π₂
        (funext fun z ↦ z.property.symm) γ e)).symm

section Orbits

variable (cov₁ : IsCoveringMap f₁) (cov₂ : IsCoveringMap f₂) (b : B)

local notation "G" => FundamentalGroup B b
local notation "F₁" => Set.preimage f₁ (Singleton.singleton b : Set B)
local notation "F₂" => Set.preimage f₂ (Singleton.singleton b : Set B)
local notation "FP" =>
  Set.preimage (fun z : Function.Pullback f₁ f₂ ↦ f₁ (Function.Pullback.fst z))
    (Singleton.singleton b : Set B)

local notation "A₁" => cov₁.fundamentalGroupMulAction b
local notation "A₂" => cov₂.fundamentalGroupMulAction b
local notation "AP" =>
  IsCoveringMap.fundamentalGroupMulAction (IsCoveringMap.pullback_base cov₁ cov₂) b
local notation "A₁₂" => @Prod.mulAction G F₁ F₂ _ A₁ A₂

/-- Loop equivariance uses the pullback monodromy action on the source and the
stock diagonal product of the two monodromy actions on the target. -/
theorem pullbackFiberEquiv_smul (γ : G) (e : FP) :
    Function.Pullback.fiberEquiv f₁ f₂ b
        (@SMul.smul G FP (AP).toSemigroupAction.toSMul γ e) =
      @SMul.smul G (F₁ × F₂) (A₁₂).toSemigroupAction.toSMul γ
        (Function.Pullback.fiberEquiv f₁ f₂ b e) := by
  change Function.Pullback.fiberEquiv f₁ f₂ b
      ((cov₁.pullback_base cov₂).monodromy γ e) =
    (cov₁.monodromy γ (Function.Pullback.fiberEquiv f₁ f₂ b e).1,
      cov₂.monodromy γ (Function.Pullback.fiberEquiv f₁ f₂ b e).2)
  exact cov₁.pullbackFiberEquiv_monodromy cov₂ γ e

/-- The point-fiber comparison descends to orbit classes using the existing quotient
congruence. The source action is the pullback covering's canonical action. -/
noncomputable def pullbackFiberOrbitEquivProd :
    @MulAction.orbitRel.Quotient G FP _ AP ≃
      @MulAction.orbitRel.Quotient G (F₁ × F₂) _ A₁₂ :=
  Quotient.congr (Function.Pullback.fiberEquiv f₁ f₂ b) (by
    let := A₁
    let := A₂
    let := AP
    intro e e'
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γ, (cov₁.pullbackFiberEquiv_smul cov₂ b γ e').symm.trans
        (congrArg (Function.Pullback.fiberEquiv f₁ f₂ b) hγ)⟩
    · rintro ⟨γ, hγ⟩
      refine ⟨γ, (Function.Pullback.fiberEquiv f₁ f₂ b).injective ?_⟩
      exact (cov₁.pullbackFiberEquiv_smul cov₂ b γ e').trans hγ)

/-- Evaluation on a fiber-point representative. -/
@[simp] theorem pullbackFiberOrbitEquivProd_apply_mk (e : FP) :
    cov₁.pullbackFiberOrbitEquivProd cov₂ b
        (Quotient.mk (@MulAction.orbitRel G FP _ AP) e) =
      Quotient.mk (@MulAction.orbitRel G (F₁ × F₂) _ A₁₂)
        (Function.Pullback.fiberEquiv f₁ f₂ b e) := by
  rfl

/-- The inverse orbit comparison pairs the two fiber points. -/
@[simp] theorem pullbackFiberOrbitEquivProd_symm_apply_mk (e₁ : F₁) (e₂ : F₂) :
    (cov₁.pullbackFiberOrbitEquivProd cov₂ b).symm
        (Quotient.mk (@MulAction.orbitRel G (F₁ × F₂) _ A₁₂) (e₁, e₂)) =
      Quotient.mk (@MulAction.orbitRel G FP _ AP)
        ((Function.Pullback.fiberEquiv f₁ f₂ b).symm (e₁, e₂)) := by
  rfl

/-- Over a path-connected base, diagonal fiber orbits describe all path components of
the pullback. This composes the existing monodromy-orbit/component equivalence;
neither total space is required to be path-connected or nonempty. -/
noncomputable def pullbackProdOrbitEquivZerothHomotopy [PathConnectedSpace B] :
    @MulAction.orbitRel.Quotient G (F₁ × F₂) _ A₁₂ ≃ ZerothHomotopy (f₁.Pullback f₂) :=
  (cov₁.pullbackFiberOrbitEquivProd cov₂ b).symm.trans
    ((cov₁.pullback_base cov₂).monodromyOrbitEquivZerothHomotopy b)

/-- A pair of fiber points maps to the component of the original pullback point. -/
@[simp] theorem pullbackProdOrbitEquivZerothHomotopy_apply_mk [PathConnectedSpace B]
    (e₁ : F₁) (e₂ : F₂) :
    cov₁.pullbackProdOrbitEquivZerothHomotopy cov₂ b
        (Quotient.mk (@MulAction.orbitRel G (F₁ × F₂) _ A₁₂) (e₁, e₂)) =
      ZerothHomotopy.mk
        ((Function.Pullback.fiberEquiv f₁ f₂ b).symm (e₁, e₂)).val := by
  change (cov₁.pullback_base cov₂).monodromyOrbitEquivZerothHomotopy b
    ((cov₁.pullbackFiberOrbitEquivProd cov₂ b).symm
      (Quotient.mk (@MulAction.orbitRel G (F₁ × F₂) _ A₁₂) (e₁, e₂))) = _
  rw [pullbackFiberOrbitEquivProd_symm_apply_mk,
    monodromyOrbitEquivZerothHomotopy_apply]

/-- The component of a pullback point over the basepoint maps back to its diagonal orbit. -/
@[simp] theorem pullbackProdOrbitEquivZerothHomotopy_symm_apply [PathConnectedSpace B]
    (e : FP) :
    (cov₁.pullbackProdOrbitEquivZerothHomotopy cov₂ b).symm
        (ZerothHomotopy.mk e.val) =
      Quotient.mk (@MulAction.orbitRel G (F₁ × F₂) _ A₁₂)
        (Function.Pullback.fiberEquiv f₁ f₂ b e) := by
  change cov₁.pullbackFiberOrbitEquivProd cov₂ b
    (((cov₁.pullback_base cov₂).monodromyOrbitEquivZerothHomotopy b).symm
      (ZerothHomotopy.mk e.val)) = _
  rw [monodromyOrbitEquivZerothHomotopy_symm_apply,
    pullbackFiberOrbitEquivProd_apply_mk]

end Orbits

end IsCoveringMap
