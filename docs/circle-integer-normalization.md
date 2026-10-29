# Integer normalization of the circle computation

Mathlib's quotient-covering computation already applies to the usual complex
unit circle at `1`. This guide describes its positive integer normalization,
including its value on every signed exponential-loop class. The construction
uses existing equivalences; no separate winding-number or loop-group model is
needed. The Mathlib APIs below refer to the revision recorded in the README.
This library provides characteristic equations for the covering equivalence and
for monodromy on a supplied continuous lift.

## The exact composition

Put `c = 2 * Real.pi` and `L = AddSubgroup.zmultiples c`. These are abbreviations
in this explanation. Use the supplied point
`e = ⟨0, Circle.exp_zero⟩ : Circle.exp ⁻¹' {(1 : Circle)}`.

The stock equivalence is

```lean
Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e
```

with type `FundamentalGroup Circle 1 ≃* (Multiplicative L)ᵐᵒᵖ`.
`Analysis/SpecialFunctions/Complex/Circle.lean` proves the required covering
property for this particular exponential. The instances from
`Analysis/Convex/Contractible.lean` and
`AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean` supply simple
connectivity of the real line. No circle-classification hypothesis is used.

There is a shorter lattice normalization than choosing a generator of an
abstract infinite cyclic group. The homomorphism

```lean
zmultiplesHom ℝ c : ℤ →+ ℝ
```

sends `n` to `n • c`, and its range is definitionally `L`.
It is injective: equality of its values is
`(m : ℝ) * c = (n : ℝ) * c`; cancel the nonzero positive real number `c`,
then use injectivity of the integer cast. Thus, for this injectivity proof `h`,

```lean
AddMonoidHom.ofInjective h : ℤ ≃+ L
```

is exactly the desired equivalence `A`, with `↑(A n) = n • c`.
This uses `Data/Int/Cast/Lemmas.lean` and
`Algebra/Group/Subgroup/Ker.lean`. There is no need for an additional `Infinite L`
instance, a generator-equals-top proof, or a new generic lattice equivalence.

Compose the stock equivalence, then

```lean
(MulOpposite.opMulEquiv : Multiplicative L ≃* (Multiplicative L)ᵐᵒᵖ).symm
```

and then `AddEquiv.toMultiplicative A.symm`. Denote this composition by `N` in
this explanation. Its type is
`FundamentalGroup Circle 1 ≃* Multiplicative ℤ`.
The middle map is **unop**, not inversion; it uses commutativity of `L`.
Consequently this choice sends the positive real period `2π` to the integer
`1`, not `-1`.

## Endpoint characteristic and all signed representatives

For any class `q : FundamentalGroup Circle 1` and any `n : ℤ`, the composition
has the characteristic equation

```text
N q = Multiplicative.ofAdd n
  ↔ (Circle.isCoveringMap_exp.monodromy q e).val = (n : ℝ) * c.
```

Indeed, injectivity of the two algebraic equivalences reduces the left side to
saying that the stock equivalence has value
`MulOpposite.op (Multiplicative.ofAdd (A n))`.
`IsAddQuotientCoveringMap.fundamentalGroupEquiv_apply_eq_iff`
then says that `Multiplicative.ofAdd (A n)` translates `0` to the lifted
endpoint. That translation is `↑(A n) + 0 = (n : ℝ) * c`, with no sign change.
The `_apply` lemma relates this equivalence to Mathlib's underlying
`fundamentalGroupToMulOpposite`.

More explicitly, let `γ : Path (1 : Circle) 1`, and let
`Γ : C(unitInterval, ℝ)` satisfy `Circle.exp ∘ Γ = γ` and `Γ 0 = 0`.
`IsCoveringMap.monodromy_mk_apply_eq_of_lift`, using Mathlib's uniqueness of
path lifting, identifies the monodromy endpoint with `Γ 1` directly.
The characteristic equation becomes

```text
N (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd n
  ↔ Γ 1 = (n : ℝ) * c.
```

For **every integer** `n`, take `Γ` to be
`Path.segment (0 : ℝ) ((n : ℝ) * c)`. Map it through `Circle.exp` and use
`Circle.exp_zero.symm` and `(Circle.exp_int_mul_two_pi n).symm` to cast its
endpoints to `1`. Call this loop `fₙ` in this explanation. Its function is
`t ↦ Circle.exp (c * (n : ℝ) * (t : ℝ))`, by `Path.segment_apply` and the
formula for the affine line map. Its real lift ends at `(n : ℝ) * c`, so

```text
N [fₙ] = Multiplicative.ofAdd n,
N.symm (Multiplicative.ofAdd n) = [fₙ].
```

This argument includes `n = 0` and negative `n`; it does not extrapolate from
one positive generator. Injectivity of `N` and its homomorphism law also give
`[fₘ] * [fₙ] = [fₘ₊ₙ]`. Here multiplication is Mathlib's canonical
endomorphism multiplication, `p * q = q.trans p`, not pointwise loop
multiplication.

For an arbitrary loop, if its lifted endpoint through the radian exponential
is `r`, the integer coordinate of `N` is `r / c`. Equivalently, lifting through
the period-one map `s ↦ Circle.exp (c * s)` ends at that integer itself.
Indeed, divide the radian lift by `c`; conversely, multiplying any period-one
lift by `c` gives the unique radian lift. Continuity and these identities use
only the nonzero constant `c`. Thus `N` is the lifted-endpoint map and `N.symm`
is the signed exponential-loop map. A radian endpoint `2πn` must not be
confused with a period-one endpoint `n`.

## References and credit

* Mathlib supplies the circle exponential, contractibility, generic covering and
  lifting proofs, path segments, range equivalence and type-tag equivalences.
  In particular the covering computation is in
  `Topology/Homotopy/Lifting.lean`; the opposite removal is in
  `Algebra/Group/Equiv/Opposite.lean`.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §5,
  motivates the signed exponential-loop and lifted-endpoint normalization.

This is a mathematical assembly of the existing APIs, not an additional
exported circle-computation declaration. May's mathematical motivation and
Mathlib's formalization are credited separately from redistribution rights:
no book text, figures or assets are included, and no license on the book is
inferred. This guide is original work by Formal Frontier Agents under the
repository's Apache-2.0 license.
