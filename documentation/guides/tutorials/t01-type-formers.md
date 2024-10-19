# Type Formers
In this tutorial, we will take a look at the building blocks of types that you will use often when formalizing. You will see how to define the types, how to construct their terms (their elements) and how to use their terms.

In unimath, all types have the same type `UU` (they all live in the *type universe* `UU`). If you see `X : UU` somewhere, that just means that `X` is a (or any) type.

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

## The natural numbers
The next type that we will discuss are the natural numbers. These are the 'counting numbers' 0, 1, 2, 3, …

Formally, there are two ways to make a natural number. There is a "first element" `O : nat`, which corresponds to `0`. Also, if we have `n : nat`, then there is also `S n : nat`, which corresponds to `n + 1`. For example, `3` is formally defined as `S (S (S O))`.

If we want to prove (or define) something based on some `n : nat`, we can again use induction. This induction involves two steps:

* The base case: we give our proof for `n = O`.
* The induction step: given a proof for `n = m`, we give a proof for `n = S m`.

Since every natural number consists of a finite number of `S`es and then a `O`, the combination of the two parts of the induction will reach every number eventually. For example, we can define a function `double` which doubles a natural number, and then show that `double (S n) = S (S (double n))`:
```coq
Definition double
  : nat → nat
  := nat_rect _
    O                 (* The base case *)
    (λ n x, S (S x)). (* The induction step: if `double n` gives `x`, double (n + 1) should give x + 2 *)

Lemma double_sn
  (n : nat)
  : double (S n) = S (S (double n)).
Proof.
  induction n.
  - reflexivity. (* This shows that 2 = 2 *)
  - reflexivity. (* This shows that S (S (S (S (double n)))) = S (S (S (S (double n)))) *)
Qed.
```

## Coproducts
⨿
inl inr

## Dependent sums
total2
∑
,,
pr1 pr2

## Dependent products
∏
λ
_ _
