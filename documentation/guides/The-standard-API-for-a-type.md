So suppose you want to create a type `foo`. Then you probably will need a constructor for this type, as well as accessors for its data and more related definitions. Here is an example of such an API.

```coq
(* The data of a foo is a bar, together with some additional information. *)
Definition foo_data : UU := ∑ (b: bar) (x: datum1 b), datum2 b x.

Definition make_foo_data
  (b : bar)
  (x : datum1 b)
  (y : datum2 b x)
  : foo_data
  := b ,, x ,, y.

Coercion foo_data_to_bar (x : foo_data) : bar := pr1 x.
Definition foo_data_to_datum1 (x : foo_data) : datum1 x := pr12 x.
Definition foo_data_to_datum2 (x : foo_data) : datum2 x (foo_data_to_datum1 x) := pr22 x.

(* A foo has some properties *)
Definition is_foo (f : foo) :=
  (property1 f) x
  (property2 f).

Definition make_is_foo
  (f : foo) (* Maybe make this one implicit? *)
  (H1 : property1 f)
  (H2 : property2 f)
  : is_foo f
  := H1 ,, H2.
  
Definition foo : UU :=
  ∑ (f : foo_data), is_foo f.

Definition make_foo
  (f : foo_data)
  (H : is_foo f)
  : foo
  := f ,, H.

Coercion foo_to_foo_data (f : foo) : foo_data := pr1 f.

Definition foo_has_property1 (f : foo) : property1 f := pr12 f.
Definition foo_has_property2 (f : foo) : property2 f := pr22 f.

Lemma isaprop_is_foo (f : foo_data) (* or is_foo_isaprop? *)
  : isaprop (is_foo f).
Proof.
  apply isapropdirprod.
  ...
Qed.

Lemma foo_eq
  (f g : foo)
  (H1 : (f : bar) = (g : bar))
  (H2 : foo_data_to_datum1 f = foo_data_to_datum1 g)
  (H3 : foo_data_to_datum2 f = foo_data_to_datum2 g)
  : f = g.
Proof.
  apply subtypePairEquality'.
  ...
Qed.
```