# Transports

As mentioned before in [the tutorial about paths](./t02-paths.md), if we have a type `X` and a family of types `Y : X → UU`, and if we have a path `p : x = x'` for `x x' : X`, we can 'transport' a term `y : Y x` over this path to get `transportf Y e y : Y x'`, or transport `y' : Y x'` to get `transportb Y e y' : Y x` (note that `transportb Y e` is defined as `transportf Y (!e)`). For example, if we have `m n : nat`, `Hmn : m = n` and `Hm : m ≥ 5`, and if our goal is `n ≥ 5`, `transportf (λ l, l ≥ 5) Hmn Hm` solves this goal. Note that using a transport instead of rewriting is usually not the right approach, even though it is a possibility.

Often when proving `(x ,, y) = (x' ,, y')` in `a b : ∑ x, Y x`, one will first show that `H : x = x'` and then that `transportf Y H y = y'`. However, the latter part can be really hard. In this tutorial, we will take a look at some ways to work with transports. We will take a look at

- [Avoiding transports](#avoiding-transports)
- [Existing lemmas](#existing-lemmas)
- [Custom lemmas](#custom-lemmas)


## Avoiding transports
Often, the best approach of dealing with transports is to avoid them wherever possible. It is notoriously hard to navigate through 'transport hell', so there are some techniques to make sure you encounter them as little as possible. Most of them boil down to working in small steps:
- To show that a category is univalent, instead of trying to show univalence directly it is often easiest (but cumbersome) to construct the category as a tower of displayed categories. This way, you can deduce that the category is univalent from a couple of straightforward proofs that every layer is "displayed univalent", and this avoids working with transports.
- As mentioned in [the tutorial about homotopy types](./t04-htypes.md), many goals can be closed using `setproperty`, `homset_property` or `propproperty`, regardless whether they involve transports.
- It is important to consider the kind of equivalence that you want to show. Often, the fact that transports show up means that you need to weaken the kind of equivalence that you want to prove:
  + For categories, the proper kind of equivalence is 'adjoint equivalence'. It is much easier to show than equality, and for univalent categories, adjoint equivalence is actually equivalent to equality.
  + For objects in a category, the proper kind of equivalence is isomorphism. Again, it is often much easier to show than equality, but in a univalent category, the two notions are equivalent.
  + For types (objects in the category TYPE), the proper kind of equivalence is weak equivalence.
  + Only when dealing with elements of a set (morphisms in a category, for example) is equality the most sensible kind of equivalence. In those cases, encountering transports is rare.

## Existing lemmas
If you have tried all of the above, but were unable to avoid transports, don't panic. There are lemmas in the library which can help you reduce transports to a trivial case and eliminate them.

* `transportf_set : ∏ Y X (e : x = x) (y : Y x), isaset X → transportf Y e y = y` shows that transporting over a loop `e : x = x` is trivial if `A` is a set.
* `transport_f_f : ∏ Y x y z (e : x = y) (e' : y = z) (p : Y x), transportf Y e' (transportf P e p) = transportf P (e @ e') p` can combine two nested transports if their indexed family `P` is the same. It also has siblings `transport_f_b`, `transport_b_f` and `transport_b_b`.
* `transportf_transpose_right : transportb Y e y' = y → y' = transportf Y e y` allows you to replace a `transportf` on the right side of the goal by `transportb` on the left side of the goal. It has siblings `transportf_transpose_left`, `transportb_transpose_right` and `transportb_transpose_left`.
* `idpath_transportf : ∏ Y x y, transportf Y (idpath x) y = y` shows that transporting over `idpath` is trivial.
* `transportf_const : ∏ e (Y : UU), transportf (λ _, Y) e = idfun Y` shows that when `Y` is a constant function, transporting is trivial.
* `functtransportf : ∏ (f : X → Y) (Z : Y → UU) x x' e (z : Z (f x)), transportf (λ t, Z (f t)) e z = transportf Z (maponpaths f e) z` basically allows us to move a "non-dependent" part of the indexed family to the path over which we transport. For example, in `transportf (λ aa : A × A', C⟦pr1 aa, b⟧) e`, the projection `pr1 aa : A × A' → A` does not depend on `aa`, so with `functtransportf`, this becomes `transportf (λ a : A, C⟦a, b⟧) (maponpaths pr1 e)`.

Now, most types in UniMath are parameterized: functions and morphisms have a domain and a codomain, natural transformations connect two functors, which in turn connect two categories, the type `A[n]` of `A`-lists of length `n` has both `A` and `n` as a parameter, etc. For many types and their parameters, there are lemmas about their behaviour under transports. For example:

* `transportf_fun : ∏ Y x x' (e : x = x') (f : Y x → Z), transportf (λ t, Y t → Z) e f = f ∘ transportb Y e` shows that when the domain of a function is a dependent type, and you transport the function and apply it to a value, this is the same as transporting the value backwards and applying the function.
* `idtoiso_postcompose : ∏ (C : precategory) a b b' (e : b = b') f, f · idtoiso e = transportf (λ t, a --> t) e f` (from [CategoryTheory.Core.Univalence](../../../UniMath/CategoryTheory/Core/Univalence.v)) shows that transporting a morphism in a category along a path `e` on its codomain is the same as postcomposing it with `idtoiso e`.
* `idtoiso_functor_precompose : ∏ (F : C₁ ⟶ C₂) y x₁ x₂ (e : x₁ = x₂) f, idtoiso (maponpaths F (! e)) · f = transportf (λ t, F t --> y) e f` shows that transport of a morphism with codomain `F x₁` along a path `x₁ = x₂` is the same as precomposing with `idtoiso` of the path with `F` applied to both its sides.
* ...

## Custom lemmas
Most of the time, lemmas such as those in the previous section suffice for the simple cases that you encounter once or twice. However, sometimes the dependent type `Y` is very complicated and sometimes you need a certain fact about transports multiple times.

If you need to reduce a transport to a statement without transports (for example, replacing the transport by a composition with `idtoiso`), it often helps to generalize the statement a bit, to make it work for transport over general paths `H : x = x'`, and turn it into an auxiliary lemma. In this lemma, you can use induction to trivialize the transport and turn every `idtoiso` into the identity isomorphism. Then most of the time, the goal becomes a statement about how working with the identity does not change anything.

Consider a somewhat complicated example, where we work with pairs `(X, Xdata)`, consisting of a category `X` and a D-presheaf `Xdata` on that category. Morphisms between such category-presheaf pairs are again a pair `(f, fdata)`, consisting of a backwards functor `f` between the categories and a natural transformation `fdata` from the pullback `f* Xdata` to `Ydata`. The following lemma then states that transporting such a transformation `fdata` along a path `e : f = g` is the same as precomposing it with some whiskered version of `idtoiso e`:
```coq
Local Lemma aux1
  {D : category}
  {X Y : category}
  (f g : Y ⟶ X)
  (H : f = g)
  {Xdata : X^op ⟶ D}
  {Ydata : Y^op ⟶ D}
  (fdata : functor_opp f ∙ Xdata ⟹ Ydata)
  : transportf (λ t, functor_opp t ∙ Xdata ⟹ Ydata) H fdata
    = nat_trans_comp _ _ _ (post_whisker (op_nt (z_iso_mor (idtoiso (C := [_, _]) H))) Xdata) fdata.
Proof.
  (* Induction on H replaces g by f, makes the transport trivial and turns `z_iso_mor (idtoiso H)` into the identity natural transformation *)
  induction H.
  (* The goal is now `fdata = nat_trans_comp _ _ _ (post_whisker (op_nt (nat_trans_id f)) Xdata) fdata *)
  apply (nat_trans_eq_alt _ Ydata).
  (* nat_trans_eq_alt reduces a proof about natural transformations to a pointwise proof about the morphisms at every x *)
  intro x.
  (* The goal is now `fdata x = # (pr1 Xdata) (identity (pr1 f x)) · fdata x` *)
  refine (!id_left _ @ _).
  apply (maponpaths (λ x, x · _)).
  now refine (!functor_id Xdata _ @ _).
Qed.
```
