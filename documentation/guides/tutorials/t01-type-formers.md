# Type Formers
In this tutorial, we will take a look at the building blocks of types that you will use often when formalizing. You will see how to define the types, how to construct their terms (their elements) and how to use their terms.

In unimath, all types have the same type `UU` (they all live in the *type universe* `UU`). If you see `X : UU` somewhere, that just means that `X` is a (or any) type.

We will cover
- [Function types](#function-types)
- [The type of booleans](#the-type-of-booleans)
- [The unit type](#the-unit-type)
- [The empty type](#the-empty-type)
- [Induction](#induction)
- [Direct Products](#direct-products)
- [The natural numbers](#the-natural-numbers)
- [Coproducts](#coproducts)
- [Paths](#paths)
- [Dependent sums](#dependent-sums)
- [Dependent products](#dependent-products)

## Function types
The first type that we will need to discuss is the type of functions. If we have types `X` and `Y`, we have a function type `X → Y`. We can create a function `X → Y` by bringing an argument `x : X` into the context, and constructing a term of type `Y`. For example, the constant function from any type can be defined as follows:
```coq
Definition constant_function
  (X Y : UU)
  (y : Y)
  : X → Y.
Proof.
  intro X. (* This adds x : X to the context and transforms the goal from X → Y to Y *)
  exact y.
Defined.
```
Also, if we have a function `f : X → Y`, we can use this to turn a term `x : X` into a term `f x : Y` by applying it:
```coq
Definition apply_function
  (X Y : UU)
  (f : X → Y)
  (x : X)
  : Y.
Proof.
  apply f. (* This turns the goal from Y into X *)
  exact x.
Defined.
```
We can also do this directly:
```coq
Definition apply_function'
  (X Y : UU)
  (f : X → Y)
  (x : X)
  : Y
  := f x.
```

## The type of booleans
The first basic type that we will discuss is `bool`. It has two terms, which are called `true` and `false`.

Now, if we have a term `b` of `bool` and we want to construct a term of some type `X` which is `x1` if `b` is `true`, and which is `x2` if `b` is `false`. The elimination principle `bool_rect` allows us to do this. For example, we can define negation of booleans like
```coq
Definition neg
  (b : bool)
  : bool.
Proof.
  use (bool_rect _ _ _ b). (* This branches the proof into a branch for when b is true, and a branch for when b is false *)
  - exact false. (* The value for when b is true *)
  - exact true. (* The value for when b is false *)
Defined.
```

## The unit type
One of the most basic types is the type `unit`. It is the type with exactly one term, which is called `tt`.

Its elimination principle allows us to prove things about any term of `unit` by proving them for `tt`. For example, we can show that any term of `unit` is equal to `tt`:
```coq
Lemma t_is_tt
  (x : unit)
  : x = tt.
Proof.
  use (unit_rect (λ y, y = tt) _ x). (* This changes the goal from x = tt to tt = tt *)
  reflexivity. (* This solves any goal of the form a = a *)
Qed.
```
Note that here, we need to give a function as the first argument, which tells coq how the current goal depends on `x`.

## The empty type
Now there is a type called `empty`. It is denoted `∅` and does not contain terms. Therefore, you will not encounter it often in definitions, except for 'negation': Usually, the way to express 'there are no terms in the type `X`' is by saying 'we have a function `X → ∅`'.

Its elimination principle allows us to prove anything from `e : ∅`. In logic, this is called the principle of explosion. For example, we can show that `true = false`:
```coq
Lemma true_is_false
  (e : ∅)
  : true = false.
Proof.
  use (empty_rect _ e). (* This immediately solves any goal *)
Qed.
```

## Induction
Even though it is definitely possible to work with the eliminators for types like `empty`, `unit` and `bool`, it is often easier to use the `induction` for this purpose. The `induction` tactic, when applied to a term `x : X`, will look whether there is an elimination principle for `X`, and apply the elimination principle to the current goal. This replaces all occurrences of `x` in the goal by the possible values for `x`. For example, we can replace the eliminators in the examples above by `induction`.
```coq
Definition neg'
  (b : bool)
  : bool.
Proof.
  induction b.
  - exact false.
  - exact true.
Defined.

Lemma t_is_tt'
  (x : unit)
  : x = tt.
Proof.
  induction x.
  reflexivity.
Qed.

Lemma true_is_false'
  (e : ∅)
  : true = false.
Proof.
  induction e.
Qed.
```

## Direct Products
If we have types `X` and `Y`, there is the direct product type `dirprod X Y`, usually denoted with `X × Y`. If we have some `x : X` and some `y : X`, we can construct the pair `(x ,, y) : X × Y` (the parentheses are usually optional).

If we have some `p : X × Y`, we can decompose it into parts with `induction`:
```coq
Definition dirprod_pr1'
  (X Y : UU)
  (p : X × Y)
  : X.
Proof.
  induction p as [x y].
  exact x.
Defined.
```
Lucky for us, the library already contains the functions `dirprod_pr1` and `dirprod_pr2` that extract the components from a pair:
```coq
Definition dirprod_pr2'
  (X Y : UU)
  (p : X × Y)
  : Y.
Proof.
  exact (dirprod_pr2 p).
Defined.
```

If the goal is a direct product, there is a tactic named `split`, which splits up the goal into the two parts:
```coq
Definition true_and_false
  : bool × bool.
Proof.
  split.          (* This splits up the goal into two goals `bool` *)
  - exact true.
  - exact false.
Defined.
```

## The natural numbers
The next type that we will discuss are the natural numbers. These are the 'counting numbers' 0, 1, 2, 3, …

Formally, there are two ways to make a natural number. There is a "first element" `O : nat`, which corresponds to `0`. Also, if we have `n : nat`, then there is also `S n : nat`, which corresponds to `n + 1`. For example, `3` is formally defined as `S (S (S O))`.

If we want to prove (or define) something based on some `n : nat`, we can again use induction. This induction involves two steps:

* The base case: we give our proof for `n = O`.
* The induction step: given a proof for `n = m`, we give a proof for `n = S m`.

Since every natural number consists of a finite number of `S`es and then a `O`, the combination of the two parts of the induction will reach every number eventually. For example, we can define functions `double` and `quadruple` which double and quadruple a natural number, and then show that `double (double n) = quadruple n`:
```coq
Definition double
  : nat → nat
  := nat_rect _
    O                 (* The base case *)
    (λ n x, S (S x)). (* The induction step: if `double n` gives `x`, double (n + 1) should give x + 2 *)

Definition quadruple
  : nat → nat
  := nat_rect _
    O                         (* The base case *)
    (λ n x, S (S (S (S x)))). (* The induction step: if `double n` gives `x`, double (n + 1) should give x + 2 *)

Lemma double_sn
  (n : nat)
  : double (double n) = quadruple n.
Proof.
  induction n as [ | n IHn ].
  - reflexivity. (* This shows that double (double 0) = quadruple 0 *)
  - simpl.       (* This simplifies double (double (S n)) to S (S (S (S (double n)))) *)
    rewrite IHn. (* This replaces (double (double n)) by quadruple n *)
    reflexivity. (* This shows that S (S (S (S (quadruple n)))) = S (S (S (S (quadruple n)))) *)
Qed.
```

## Coproducts
Another type that you will encounter sometimes is the coproduct (or `disjoint union`) type. We can inject terms `x : X` and `y : Y` as `inl x : X ⨿ Y` and `inr y : X ⨿ Y` ("inject left" and "inject right").

The induction principle allows us to show things about some `u : X ⨿ Y` by assuming that either `u = inl x` for some `x : X` or `u = inr y` for some `y : Y`. We will use this to construct a function that swaps the two sides of the coproduct, and show that applying it twice gives the same term back again:
```coq
Definition coprod_swap
  (X Y : UU)
  : X ⨿ Y → Y ⨿ X
  := coprod_rect _
    (λ x, inr x)    (* coprod_swap (inl x) = inr x *)
    (λ y, inl y).   (* coprod_swap (inr y) = inl y *)

Lemma coprod_swap_twice
  (X Y : UU)
  (u : X ⨿ Y)
  : coprod_swap Y X (coprod_swap X Y u) = u.
Proof.
  induction u as [x | y].
  - reflexivity. (* This shows that coprod_swap _ _ (coprod_swap _ _ (inl x)) = inl x *)
  - reflexivity. (* This shows that coprod_swap _ _ (coprod_swap _ _ (inr y)) = inr y *)
Qed.
```

## Paths
Now we will take a look at equalities, which are also called 'paths', because of their role in homotopy type theory. If we have some type `X : UU` and two terms `x y : X`, then we have the type of paths `x = y`. There is only one basic constructor for this type: `idpath x : x = x`.

In UniMath, path types are sometimes inhabited by multiple distinct terms. For example, `bool = bool` has two terms, one of which is the identity:
```coq
Definition bool_idpath
  : bool = bool
  := idpath _.
```
If we have some `x : X` and want to show something about `p : x = y` for all `y : X`, then the induction principle allows us to assume that `p = idpath x`:
```coq
Lemma path_symmetry
  (X : UU)
  (x y : X)
  (p : x = y)
  : y = x.
Proof.
  induction p. (* This removes y from the context and replaces it by x everywhere *)
  exact (idpath x).
Qed.
```

## Dependent sums
Now we get to the 'dependent' types, which turn the type theory of coq into a dependent type theory. They both start from a 'family of types', given by a function `Y : X → UU`.

The dependent sum is written as `∑ (x : X), Y x` (which is notation for `total2 Y`). Its terms are pairs `(x ,, y)` (notation for `tpair Y x y`), where `x : X` and `y : Y x`. The direct product `X × Z` is a special case of this, with `Y` given by the constant family `λ _, Z`.

We can use the dependent sum to create this toy example of a type of 'equal terms'. An equal term of some `x : X` is given by some `y : X`, together with a path `p : y = x`.
```coq
Definition equal_term
  (X : UU)
  (x : X)
  : UU
  := ∑ (y : X), y = x.
```
A trivial example of a term of this type, is given by the identity path on `x`:
```coq
Definition identity_equal_term
  (X : UU)
  (x : X)
  : equal_term X x
  := x ,, idpath x.
```
The induction principle for the dependent sum, splits up the pairs into their first and second components. The library also contains functions for this, called `pr1` and `pr2`.
```coq
Definition equal_term_term
  (X : UU)
  (x : X)
  (y : equal_term X x)
  : X.
Proof.
  induction y as [y p]. (* Gives y : X and p : x = y *)
  exact y.
Defined.

Definition equal_term_equality
  (X : UU)
  (x : X)
  (y : equal_term X x)
  : equal_term_term X x y = x
  := pr2 y.
```

### Subtypes
Using dependent sums, we can also create subtypes. If we have a predicate `P : X → UU`, the type of `x : X` such that `P x`, is given by `∑ x, P x`. For example, the type of 'even' natural numbers can be given by
```coq
Definition is_even
  (n : nat)
  : UU
  := ∑ m, n = 2 * m.

Definition even_numbers
  : UU
  := ∑ n, is_even n.
```

## Dependent products
If the dependent sum is a more general form of the direct product, the dependent product is a more general form of the function type. If we have a family of types `Y : X → UU`, then the terms `f : ∏ (x : X), Y x` of the dependent product turn any `x : X` into some `f x : Y x`. The function type `X → Z` is a special case, where `Y` is given by the constant family `λ _, Z`.

For example, we can define the type of
```coq
Definition all_terms_are_equal
  (X : UU)
  (x : X)
  : UU
  := ∏ (y : X), y = x.
```
Just like with functions, we can create a term of the dependent product by bringing an argument `x : X` into the context, and producing a term of `Y x`.
```coq
Definition all_terms_are_equal_unit
  : all_terms_are_equal unit tt.
Proof.
  intro t.      (* This turns the goal into t = tt *)
  induction t.  (* This replaces t by tt *)
  reflexivity.
Defined.
```
We can use a term of `all_terms_are_equal X x` to show that any two values of a function from `X` must be equal:
```coq
Lemma all_terms_are_equal_fun
  (X Y : UU)
  (x : X)
  (H : all_terms_are_equal X x)
  (f : X → Y)
  (y z : X)
  : f y = f z.
Proof.
  pose (H y) as Hy. (* This adds Hy : y = x to the context *)
  rewrite Hy.       (* This rewrites f y to f x *)
  pose (H z) as Hz. (* This adds Hz : z = x to the context *)
  rewrite Hz.       (* This rewrites f z to f x *)
  reflexivity.      (* This shows that f x = f x *)
Qed.
```
