# Integer coordinates for circle fundamental groups

Import
`FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle`, or the
`FundamentalGroupoids` root, for the public coordinate equivalences

```lean
AddCircle.fundamentalGroupEquivInt {T : ℝ} (hT : T ≠ 0) :
    FundamentalGroup (AddCircle T) 0 ≃* Multiplicative ℤ

Circle.fundamentalGroupEquivInt :
    FundamentalGroup Circle 1 ≃* Multiplicative ℤ
```

The signed-period and complex-circle formalization originates in
[Sphere Topology](https://github.com/FormalFrontier/sphere-topology/blob/4a2b822f12e7f2b4255dfea5363265277defa35e/SphereTopology/Homotopy/Circle.lean),
by Formal Frontier Agents. The constructions use Mathlib's covering,
simply-connectedness, path and algebraic-equivalence APIs; no separate
winding-number or loop-group model is introduced. The pins are recorded in the
[README](../README.md#building).

## Signed additive-circle coordinates

For every real `T` and integer `n`, `AddCircle.loop T n` projects the segment
from `0` to `T * n` into `AddCircle T`. The public evaluation and lifting laws are
`AddCircle.loop_apply`, `AddCircle.coe_loop` and `AddCircle.liftPath_loop`.
For `hT : T ≠ 0`,

```text
AddCircle.fundamentalGroupEquivInt hT
    (FundamentalGroup.fromPath ⟦AddCircle.loop T n⟧)
  = Multiplicative.ofAdd n.
```

Use `AddCircle.fundamentalGroupEquivInt_loop` for this normalization,
`fundamentalGroupEquivInt_symm_apply` to construct the inverse image, and
`eq_loop_fundamentalGroupEquivInt` to put an arbitrary class in signed-loop
normal form. `fundamentalGroupEquivInt_unique` says that these values on all
integer loops determine the equivalence uniquely.

The construction first applies
`AddCircle.isAddQuotientCoveringMap_coe T`'s simply connected covering
equivalence. Its target is the opposite of
`Multiplicative (AddSubgroup.zmultiples T)`. The homomorphism

```lean
zmultiplesHom ℝ T : ℤ →+ ℝ
```

is injective for `T ≠ 0`, and `AddMonoidHom.ofInjective` identifies `ℤ` with
its range, `AddSubgroup.zmultiples T`. The coordinate is the covering
equivalence followed by commutative **unop**, then the inverse of this range
equivalence. Unop is not inversion and introduces no sign change.

The normalization uses `T`, not `|T|`. A negative period therefore gives a
prescribed generator with decreasing real lift and integer coordinate `+1`.
Replacing the signed period by its absolute value would change this convention.
At `T = 0` the covering still exists, but every `AddCircle.loop 0 n` is constant
(`AddCircle.loop_zero_period`), and the fundamental group is trivial, not `ℤ`.
The nonzero hypothesis belongs on the coordinate equivalence, not on the loop
or covering definitions. For nonzero `T`, `AddCircle.loop_one_ne_one` supplies
the nonidentity generator law.

For any supplied real lift `Γ` of a loop `γ`, starting at zero,
`AddCircle.fundamentalGroupEquivInt_apply_eq_iff` gives

```text
AddCircle.fundamentalGroupEquivInt hT (FundamentalGroup.fromPath ⟦γ⟧)
    = Multiplicative.ofAdd n
  ↔ Γ 1 = T * (n : ℝ).
```

`AddCircle.liftPath_apply_one` states the endpoint formula directly for
Mathlib's chosen lift.

## The complex circle and its positive generator

`Circle.loop n` is the image of `AddCircle.loop 1 n` under the period-one
circle homeomorphism, with endpoints cast to `1`. Its public evaluation law is

```text
Circle.loop n t = Circle.exp (2 * Real.pi * (n : ℝ) * (t : ℝ)).
```

Thus `+1` is counterclockwise, `-1` is clockwise, and `0` is constant.
`Circle.coe_loop_apply` gives the same formula as a complex exponential.
The period-one transported path and a radian segment projected by `Circle.exp`
have this same evaluation; their constructions are not definitionally the same.
Use `Circle.loop_apply` and path extensionality rather than `rfl` to compare them.

`Circle.fundamentalGroupEquivInt` transports the additive-circle coordinate
through `AddCircle.homeomorphCircle` at period one. Its implementation uses the
homeomorphism's induced fundamental-groupoid equivalence,
`fullyFaithfulFunctor.mulEquivEnd`, and equality-index transport by
`eqToIso.conj`. It is the map induced by that homeomorphism, not a choice of
preimages arranged to give a generator value.

The characteristic API includes:

- `Circle.fundamentalGroupEquivInt_loop`: every signed loop has coordinate `n`;
- `Circle.fundamentalGroupEquivInt_symm_apply`: the inverse constructs its class;
- `Circle.fromPath_loop_add`: the class of `loop (m + n)` is the product of
  the classes of `loop m` and `loop n`;
- `Circle.loop_one_ne_one`: the positive full turn is not the identity class.

Multiplication retains Mathlib's endomorphism convention: the right factor is
traversed first. It is not pointwise multiplication of paths.

For every nonzero signed period, `AddCircle.homeomorphCircle_loop` identifies
the image of `AddCircle.loop T n` with `Circle.loop n`.
`AddCircle.fundamentalGroupEquivInt_homeomorphCircle` states equality of the
coordinates under the induced `FundamentalGroup.mapOfEq`. In particular, the
negative-period prescribed generator also maps to the positive complex loop.

## Radian and period-one endpoints

`Circle.exp` uses radians. `Circle.liftPath_apply_one` says that its zero-start
lift of `γ` ends at

```text
2 * Real.pi *
  ((Circle.fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦γ⟧)).toAdd : ℝ).
```

By uniqueness of lifts, any supplied radian lift starting at zero has this
endpoint. Dividing it by `2 * Real.pi` gives the integer coordinate. By contrast,
`Real.fourierChar s = Circle.exp (2 * Real.pi * s)` is period one.
`Circle.fundamentalGroupEquivInt_apply_eq_iff` applies to a supplied continuous
lift `Γ` through this map, starting at zero, and states

```text
Circle.fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦γ⟧)
    = Multiplicative.ofAdd n
  ↔ Γ 1 = (n : ℝ).
```

A radian endpoint `2πn` must not be confused with a period-one endpoint `n`.
The [circle verification module](../FundamentalGroupoidsTest/Topology/Covering/Circle.lean)
uses these public endpoint and signed-loop laws. Its private
`integerNormalization` and `signedExpLoop` names are only aliases for the public
coordinate and loop.

## Integer power-map consumers

Write `N = Circle.fundamentalGroupEquivInt` and let `Pₙ` be the continuous map
`z ↦ z ^ n`, with basepoint equality `one_zpow n`. For every `n : ℤ` and every
`q : FundamentalGroup Circle 1`, the same verification module proves privately

```text
N (FundamentalGroup.mapOfEq Pₙ (one_zpow n) q)
  = Multiplicative.ofAdd (n * (N q).toAdd).
```

The consumer uses the public inverse-loop law to represent `q` by
`Circle.loop (N q).toAdd`. On that representative, `Circle.loop_apply` and
`Circle.exp_zsmul` give the equality of paths

```text
(Circle.loop m mapped by Pₙ, with endpoints cast by one_zpow n)
  = Circle.loop (n * m).
```

`FundamentalGroup.mapOfEq_apply` gives the corresponding loop-class equation,
and `Circle.fundamentalGroupEquivInt_loop` computes its coordinate. This is a
consumer of the public normal form, not a second period-lattice construction.
The argument covers zero and negative exponents without assuming that the power
map is a covering. At zero the induced homomorphism is zero in integer
coordinates; a negative exponent reverses the sign. The squaring-map example
uses this formula to distinguish its image from the identity under the
fundamental-group functor on the based-homotopy category.

For general circle self-maps and arbitrary return paths,
[Sphere Topology's degree API](https://github.com/FormalFrontier/sphere-topology/blob/4a2b822f12e7f2b4255dfea5363265277defa35e/SphereTopology/Homotopy/CircleDegree.lean)
provides `Circle.fundamentalGroupEquivInt_map` and `Circle.degree_zpow`.
That broader degree, free-homotopy and fixed-point theory is not a dependency of
the Fundamental Groupoids coordinate module. Joint users must select a Sphere
Topology version whose old circle module publicly imports this canonical module,
not a version defining another copy of these names.

## References and credit

- J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §5,
  pp. 8–9, for signed loops and lifted endpoints, and §7, p. 10, for degree and
  power maps. The signed-period additive-circle formulation generalizes the
  positive circle normalization.
- Formal Frontier Agents' existing circle formalization in Sphere Topology,
  linked above, supplies the coordinate definitions and proofs.
- Mathlib supplies the quotient covering and monodromy formalization by Junyan
  Xu, additive and complex circles, contractibility, paths and group equivalences.

May's mathematics and the prior formalizations are credited separately from
redistribution rights: no book text, figures or assets are included, and no
license on the book is inferred. This guide is original work by Formal Frontier
Agents under the repository's Apache-2.0 license.
