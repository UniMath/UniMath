# Opaqueness?
In coq, there is something called "Opaqueness". Usually, the contents of a definition, or a proof that is closed with `Defined`, are visible to coq. This means that `simpl` or `cbn` can unfold such a definition, but also that coq needs to move it around and manipulate it when proving things about it. Sometimes that is a good thing. It would be hard to prove anything about a specific function `nat -> nat` if we did not have access to its definition. On the other hand, if we prove a proposition, for example `forall n, f n = f (2 * n) + f(2 * n + 1)`, we are probably not interested in the proof term itself, but only in the fact that it exists. In fact, the proof term would only constitute clutter in subsequent goals and definitions where we would use it. In such cases, it is wise to make it opaque. Properly managing opaqueness/transparency saves at most one or two minutes per definition, which for a large development can make a great difference in evaluation time.

## When?
A good rule of thumb is: a proof of a proposition (something of type `T` such that `isaprop T` holds) should be made opaque. So anything of type `forall x y, f x y = g y x` (for `f` and `g` functions into a `hSet`) or `forall n, n > 5, n * n > 5 n` should be made opaque, whereas something of type `nat -> nat` or `forall n, stn (S n) = unit ⨿ stn n` should not.

However, there are always exceptions. An example is inverses: `isweq` and `is_z_isomorphism` are propositions, but in many cases, being able to expand the inverse function (when using `isweq_iso`) or morphism is very useful. So the better (but more vague) rule of thumb is: "Make something opaque iff people will probably not be interested in its exact definition".

## How?
There are two common ways to make something opaque. The first is closing a proof with `Qed`. It is important to properly split your definitions. By having everything split up in multiple identifiers, you can make the right parts opaque. This also makes goals cleaner and more readable, and unification becomes a bit nicer, because computation gets blocked more. For example:
```coq
Definition example_function (n : nat) : nat.
Proof.
  induction n as [ | n' IHn'].
  - exact O.
  - exact (S (S IHn')).
Defined.

Lemma example_proof (n : nat) : example_function n = 2 * n.
Proof.
  induction n as [ | n' IHn'].
  - apply idpath.
  - refine (maponpaths (λ x, S (S x)) IHn' @ _).
    apply (maponpaths S).
    apply plus_n_Sm.
Qed.

Definition doubling_function : ∑ f, ∏ n, f n = 2 * n
  := example_function ,, example_proof.
```
Another example: when you have a functor into a functor category, then it is good to make a separate definition for the action on objects. This action on objects is given by a functor, and for that one, it is good to split it as well.

Now, if you only want to make a (small) part of your definition opaque and you do not want to split the definition into separate definitions and lemmas, you can use `abstract (sequence_of_tactics).` For example:
```coq
Definition doubling_function : ∑ f, ∏ n, f n = 2 * n.
Proof.
  use tpair.
  - intro n.
    induction n as [ | n' IHn'].
    + exact O.
    + exact (S (S IHn')).
  - abstract (
      intro n;
      induction n as [ | n' IHn'];
      [ apply idpath
      | refine (maponpaths (λ x, S (S x)) IHn' @ _);
        apply (maponpaths S);
        apply plus_n_Sm ]
    ).
Defined.
```
Note that in this form, you cannot go through the proof step by step, and even though it is a bit more compact, it is less readable. It is therefore wise to use `abstract` as little as possible.
