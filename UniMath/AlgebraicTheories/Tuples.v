Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Definition extend_tuple
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  : stn (S n) → T.
Proof.
  intro i.
  induction (invweq (weqdnicoprod _ lastelement) i) as [a | ].
  - exact (f a).
  - exact last.
Defined.

Definition extend_tuple_dep
  {n : nat}
  {T : UU}
  {A : T → UU}
  {f : stn n → T}
  {last : T}
  (af : ∏ i, A (f i))
  (alast : A last)
  : ∏ (i : stn (S n)), A (extend_tuple f last i).
Proof.
  intro i.
  unfold extend_tuple.
  induction (invweq (weqdnicoprod _ lastelement) i) as [a | ].
  - exact (af a).
  - exact alast.
Defined.

Lemma extend_tuple_dep_const
  {T A : UU}
  {n : nat}
  {f : stn n → T}
  {last : T}
  (af : stn n → A)
  (al : A)
  : extend_tuple_dep (T := T) (A := λ _, A) (f := f) (last := last) af al = extend_tuple af al.
Proof.
  apply funextsec.
  intro i.
  unfold extend_tuple, extend_tuple_dep.
  now induction (invweq (weqdnicoprod _ lastelement) i).
Qed.

Lemma extend_tuple_i
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  (i : nat)
  (Hi1 : i < S n)
  (Hi2 : i < n)
  : extend_tuple f last (i ,, Hi1) = f (make_stn _ i Hi2).
Proof.
  unfold extend_tuple.
  assert (H : invweq (weqdnicoprod n lastelement) (i ,, Hi1) = inl (make_stn _ i Hi2)); [ | now rewrite H].
  apply (invmaponpathsweq (weqdnicoprod n lastelement)).
  refine (homotweqinvweq _ _ @ _).
  apply subtypePairEquality.
  - intro.
    apply isasetbool.
  - unfold di.
    induction (natlthorgeh (make_stn n i Hi2) (lastelement (n := n))) as [a | a].
    + apply idpath.
    + induction (natgehtonegnatlth _ _ a Hi2).
Qed.

Lemma extend_tuple_last
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  (i : stn (S n))
  (Hi : stntonat _ i = n)
  : extend_tuple f last i = last.
Proof.
  unfold extend_tuple.
  assert (H : invweq (weqdnicoprod n lastelement) i = inr tt); [ | now rewrite H].
  apply (invmaponpathsweq (weqdnicoprod n lastelement)).
  refine (homotweqinvweq _ _ @ _).
  apply subtypePairEquality.
  - intro.
    apply isasetbool.
  - apply Hi.
Qed.

Lemma extend_tuple_dni_lastelement
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  (i : stn n)
  : extend_tuple f last (dni_lastelement i) = f i.
Proof.
  apply extend_tuple_i.
Qed.

Lemma extend_tuple_lastelement
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  : extend_tuple f last (lastelement) = last.
Proof.
  now apply extend_tuple_last.
Qed.

Lemma extend_tuple_eq
  {T : UU}
  {n : nat}
  {last : T}
  {f : stn n → T}
  {g : stn (S n) → T}
  (Hf : ∏ i, f i = g (dni_lastelement i))
  (Hlast : last = g lastelement)
  : extend_tuple f last = g.
Proof.
  apply funextfun.
  intro i.
  refine ((idpath _ : (_ = coprod_rect _ _ _ (invmap _ _))) @ _ @ maponpaths g (homotweqinvweq (weqdnicoprod n lastelement) i)).
  induction (invmap (weqdnicoprod n lastelement) i).
  - exact (Hf a @ maponpaths (λ x, g (x a)) (!replace_dni_last _)).
  - exact Hlast.
Qed.
