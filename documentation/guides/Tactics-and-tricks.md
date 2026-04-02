When one works with coq, there are many tactics that one learns to wield. Here is a list of some useful tactics:

### The introduction tactics

The tactic `intro a`, will try to unfold the current goal to the form `∏ (a : A), G` and will then bring `a : A` into the context as a variable.

There is also the variant `intro` (without the `a`), in which case coq will come up with a name for the variable. You should only do this if you do not use the variable anywhere, because the name that coq gives the variable may change in the future, and you do not want your proof to break by such a change.

There is also the multi-variable version `intros a1 a2 ... an`, which is equivalent to `intro a1; ...; intro an`. The tactic `intros` (without `a1 ... an`), when applied to a goal of the form `∏ (a1 : A1) ... (an : An), G` will bring `a1`, ..., `an` as variables into the context. However, it will not do any unfolding.

### The "apply this proof term" tactics
There are four tactics that have similar purposes: `exact`, `apply`, `refine` and `use`. You give these a proof term, and they will try to match that term to the goal.

| | Does not allow for holes | Allows for holes |
|---|---|---|
|Needs the entire proof term | `exact` | `refine` |
|Does not need the entire proof term | `apply` | `use` |

Two of them need the entire proof term, whereas the two others don't. For example, with a hypothesis like `H1 : ∏ (x : unit), x = tt` and a goal `y = tt`, one can `apply H1`, but not `exact H1`. The latter should be `exact (H1 y)` or `exact (H1 _)`. The other difference is that two of the tactics allow one to give holes that need to be filled in later, whereas the others don't. For example

```coq
Definition example1 (A B C : UU) (f : A -> B -> C) (g : A -> B) (a : A) : C.
Proof.
  refine (f (g _) _).
  - exact a.
  - exact a.
Defined.
```
We could also `use (f (g _))` instead of the line with `refine`, but for example `apply (f (g _))` would not work.

One common application of `refine` is to show an equality in small steps, rewriting one part at a time with statements like
```coq
refine (maponpaths (λ x, _ (_ x) _) (H1 _ p) @ _).
```
This replaces the left hand side of the equality `H1 _ p` with the right hand side, in some part (specified by the `_ (_ x) _`) of the left hand side of the goal.

### Induction
Induction is a useful tool for a couple of use cases:
* When you want to do [path induction](https://ncatlab.org/nlab/show/inductive+type#PathInduction) on a path `p: a = b`, `induction p` achieves this. This allows you to prove things about `p`, by just proving it for the case that `b` is definitionally equal to `a` and `p` definitionally equal to `idpath a`.
* In the proofs about the natural numbers, one regularly sees an `induction n as [| n' IHn]`, which allows one to prove a property about `n` by proving it for `0`, and for `S n'` assuming that it holds for `n'`.
* If we have `p : A × B`, `induction p as [p1 p2]` will split `p` into its components.
* If we have `p : A ⨿ B`, `induction p as [p1 | p2]` will do case distinction on whether `p` is in the left or the right component.
* If we have `p : ∅`, `induction p` will close the goal (as will `apply (fromempty p)`).

### Higher-level tactics
These tactics act on a (sequence of) tactics `t`.

The tactic `now t` will execute `t` and then close the goal if it has become trivial (and else it will fail).

If `t` closes the goal, the tactic `abstract t` will execute `t` and make the proof term produced by `t` opaque (see [On Opaqueness](./Opaqueness.md)). This is useful if you are, for example, defining a (not too complicated) functor, which needs two pieces of data, but also two proofs, and you don't want to split it yet into two (or one) proofs with `Defined` and two (or one) proofs with `Qed`.

The tactic `do n t` will try to execute `t` exactly `n` times (and fail if `t` fails before `n` executions are reached).

The tactic `repeat t` will repeat `t` as many times as possible. Its use is discouraged in favor of `do n t` because the behaviour of `repeat t` is in some sense "less predictable", which means that changes in a definition or lemma upstream can result in `repeat t` performing less (or more) repetitions, which can cause problems in the rest of the proof in which the `repeat` occurs.

### pose and assert
For building a proof term piece by piece, as well as for inspecting (the type of) a term, `pose` is a very useful tactic. For example, in
```coq
Definition example2 (A B C : UU) (f : A -> B -> C) (g : A -> B) (a : A) : C.
Proof.
  pose (b := g a).
  exact (f a b).
Defined.
```

A very similar tactic is `assert`, but it allows one to write a kind of "sublemma" instead of giving the full proof term at once. For example:
```coq
Definition example3 (A B C : UU) (f : A -> B -> C) (g : A -> B) (a : A) : C.
Proof.
  assert (b : B).
  {
    apply g.
    exact a.
  }
  exact (f a b).
Defined.
```

### Commands
The command `Locate x` will show in which package the definition for `x` can be found. Often, the definition of an object or function (for example `transportf`, `isaset`) is followed by lemmas that prove properties about it.

The command `Search (pattern)` will show all definitions that contain `pattern` (very useful if you are looking for the name of that one lemma). For example
```coq
Search (transportf). (* Just show all definitions and lemmas about transports *)
Search (_ < 0). (* when trying to find the lemma that shows that a natural number cannot be less than 0 *)
Search ((_ ⟶ _) → (_ ⟶ _) → (_ ⟶ _)). (* when trying to find out what functor composition is called *)
```

The command `Time x` (for example `Time apply H1` or `Time Qed`) will execute `x` and then show how much time elapsed. Very useful to check whether your optimization actually made your code run faster.

The commands `Set` and `Unset` influence the behaviour of coq in the rest of the document. When debugging, setting some of these flags might come in handy:
```coq
Unset Printing Notations.
Set Printing Coercions.
Set Printing Implicit.
```
