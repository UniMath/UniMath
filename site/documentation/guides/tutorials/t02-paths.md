# Paths

In this tutorial, we will cover paths. We will talk about how paths can be constructed. Among other things, we will talk about lemmas that are often used for constructing paths.

We will cover
- [Paths as an equivalence relation](#paths-as-an-equivalence-relation)
- [Maponpaths](#maponpaths)
  - [Variants](#variants)
- [Functions](#functions)
- [Direct products](#direct-products)
- [Dependent sums](#dependent-sums)
  - [Subtypes](#subtypes)
- [Dependent products](#dependent-products)

## Paths as an equivalence relation
We have already seen the `reflexivity` tactic, which uses the fact that paths are 'reflexive' (because of the existence of `idpath`). There is also the `symmetry` tactic, which turns a goal `x = y` into the goal `y = x`. Lastly, there is the `transitivity a` tactic, which splits a goal `x = y` into `x = a` and `a = y`:
```coq
Lemma path_inv_transitivity
  (X : UU)
  (x y z : X)
  (p : x = y)
  (q : y = z)
  : z = x.
Proof.
  symmetry.       (* This turns the goal into x = z *)
  transitivity y. (* This splits the goal into x = y and y = z *)
  - exact p.
  - exact q.
Qed.
```
If you do not yet want to provide `a`, you can use `etrans` instead. There is also some notation related to this: `!p` inverts the path `p` (swaps the sides), and `p @ q` composes `p` and `q`:
```coq
Definition path_inv_transitivity'
  (X : UU)
  (x y z : X)
  (p : x = y)
  (q : y = z)
  : z = x
  := !(p @ q).
```

## Maponpaths
Suppose that your goal is `f x = f x'`, and you want to show this by proving that `x = x'`. Then you can use the lemma
```coq
maponpaths : ∏ (f : X → Y), x = x' → f x = f x'.
```
Note that you can provide a 'custom' function `f` for this:
```coq
Lemma postcompose_path_path
  (X : UU)
  (x y z : X)
  (p q : x = y)
  (r : y = z)
  (H : p = q)
  : p @ r = q @ r.
Proof.
  apply (maponpaths (λ e, e @ r)). (* Here, f postcomposes paths with r *)
  exact H.
Defined.
```

### Variants
There is also a series of variants of `maponpaths`. For example, `maponpaths_2` shows that `f x y = f x' y` from `x = x'` and `maponpaths_12` shows that `f x y = f x' y'` from `x = x'` and `y = y'`:
```coq
Lemma compose_path_path
  (X : UU)
  (x y z : X)
  (p q : x = y)
  (r s : y = z)
  (H1 : p = q)
  (H2 : r = s)
  : p @ r = q @ s.
Proof.
  apply maponpaths_12.
  - exact H1.
  - exact H2.
Defined.
```
Take a look at [MoreFoundations/PartA](../../../UniMath/MoreFoundations/PartA.v) for more variants, like `maponpaths_1234`.

## Functions
Now we will take a look at lemmas for specific type formers. We will start with functions.

If you want to show that two functions are equal, you can use 'function extensionality', which shows that functions are equal if for every input, their outputs are equal:
```coq
Lemma isaprop_function_to_unit
  (X : UU)
  (f g : X → unit)
  : f = g.
Proof.
  apply funextfun.        (* This changes the goal to ∏ x, f x = g x *)
  intro x.
  induction (f x), (g x). (* This replaces f x and g x by tt *)
  reflexivity.
Qed.
```
Conversely, if you have an equality of functions, and you want to show that for some input, their inputs are equal, you can either use `maponpaths`, but there is also a specialized function `eqtohomot`:
```coq
Lemma function_value_path
  (X : UU)
  (f : X → unit)
  (x : X)
  : f x = tt.
Proof.
  apply (eqtohomot (g := λ _, tt)). (* This changes the goal to f = (λ _, tt) *)
  apply (isaprop_function_to_unit).
Qed.
```
Note that in this particular case, induction on `f x` would have sufficed:
```coq
Lemma function_value_path'
  (X : UU)
  (f : X → unit)
  (x : X)
  : f x = tt.
Proof.
  induction (f x).
  reflexivity.
Qed.
```

## Direct products
If you want to show that `(x ,, y) (x' ,, y') : X × Y` are equal, by showing that `x = x'` and `y = y'`, you can use
```coq
pathsdirprod : x1 = x2 → y1 = y2 → make_dirprod x1 y1 = make_dirprod x2 y2.
```
If you have pairs `p p' : X × Y`, of which you do not yet have the individual components, you can instead use
```coq
dirprod_paths : pr1 p = pr1 p' → pr2 p = pr2 p' → p = p'.
```

```coq
Lemma isaprop_unit_pair
  (x y : unit × unit)
  : x = y.
Proof.
  apply dirprod_paths.  (* This splits up the goal into pr1 x = pr1 y and pr2 x = pr2 y *)
  - induction (pr1 x), (pr1 y).
    reflexivity.
  - induction (pr2 x), (pr2 y).
    reflexivity.
Qed.
```
Conversely, if you have some proof that `p = p'` and you want to show that `dirprod_pr1 p = dirprod_pr1 p'`, there is no special lemma, but you can use `maponpaths dirprod_pr1`. The same goes for `dirprod_pr2`.

## Dependent sums
Since direct products are a special case of dependent sums, their paths behave similarly. If want to show that `(x ,, y) (x' ,, y') : ∑ (x : X), Y x` are equal, you can use `total2_paths_f` or `total2_paths_b`. These split up the goal into `H : x = x'` and `transportf Y H y = y'` or `y = transportb Y H y'`. The transports are because `y` lives in `Y x` and `y'` lives in `Y x'`, and these types are not definitionally equal, so we need to transport over `H` to compare `y` and `y'`.
```coq
Definition combine_dependent_sum_paths
  (X : UU)
  (Y : X → UU)
  (x x' : X)
  (y : Y x)
  (y' : Y x')
  (H : ∑ (Hx : x = x'), transportf Y Hx y = y')
  : (x ,, y) = (x' ,, y').
Proof.
  induction H as [Hx Hy].
  use total2_paths_f.
  - exact Hx.
  - exact Hy.
Defined.
```
Conversely, for a proof `p : (x ,, y) = (x' ,, y')`, there are two specialized lemmas to get paths on the components:
```coq
base_paths : ∏ (a b : ∑ y, B y), a = b → pr1 a = pr1 b.
fiber_paths : ∏ (p : u = v), transportf (λ x : A, B x) (base_paths u v p) (pr2 u) = pr2 v.
```

```coq
Definition split_dependent_sum_paths
  (X : UU)
  (Y : X → UU)
  (x x' : X)
  (y : Y x)
  (y' : Y x')
  (H : (x ,, y) = (x' ,, y'))
  : ∑ (H : x = x'), transportf Y H y = y'.
Proof.
  use tpair.
  - exact (base_paths (x ,, y) (x' ,, y') H).
  - exact (fiber_paths H).
Defined.
```

### Subtypes
When `Y` is a predicate, the dependent sum `∑ x, Y x` is a subtype of `X`. In that case, it suffices to show that `x = x'`. You can use either of the following, depending on whether you have a dependent pair `p` or two components `(x ,, y)`.
```coq
subtypePath :         isPredicate Y → pr1 p = pr1 p' → p = p.
subtypePairEquality : isPredicate Y → x = x' → x,, y = x',, y'.
```
For example, we can show that `iscontr X` is a proposition if `X` is a set. In a set, there is at most one path `x = y` between any two terms `x y : X`. See [tutorial 4](./t04-htypes.md) for more information about sets.
```coq
Lemma isaprop_iscontr
  (X : hSet)
  (x x' : ∑ (x : X), (∏ y, y = x))
  : x = x'.
Proof.
  apply subtypePath.      (* This splits the goal into `isPredicate is_even` and `pr1 m = pr1 m'` *)
  - intro y.              (* This changes the goal to `isaprop (∏ y', y' = y)` *)
    apply impred_isaprop. (* This uses a lemma to swap the `isaprop` with the `∏ y'` *)
    intro y'.
    apply setproperty.    (* If `X` is a set, `y' = y` is a proposition by definition *)
  - apply (pr2 x').
Qed.
```

## Dependent products
The lemmas `funextfun` and `eqtohomot` are special cases of two lemmas for dependent products:
```coq
funextsec :     ∏ Y (f g : ∏ x : X, Y x), (∏ (x : X), f x = g x) → f = g.
toforallpaths : ∏ Y (f g : ∏ x : X, Y x), f = g → (∏ (x : X), f x = g x).
```
For example, we can show that any two terms ('sections') of a dependent product over the empty type are equal:
```coq
Definition isaprop_empty_product (P : empty -> UU)
  (f g : (∏ x, P x))
  : f = g.
Proof.
  apply funextsec.
  intro x.
  induction x.
Qed.
```
