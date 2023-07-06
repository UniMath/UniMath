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

Lemma extend_tuple_dni_lastelement
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  (i : stn n)
  : extend_tuple f last (dni_lastelement i) = f i.
Proof.
  unfold extend_tuple.
  assert (H : invweq (weqdnicoprod n lastelement) (dni_lastelement i) = inl i); [ | now rewrite H].
  apply (invmaponpathsweq (weqdnicoprod n lastelement)).
  refine (homotweqinvweq _ _ @ maponpaths (λ x, x i) (!replace_dni_last _)).
Qed.

Lemma extend_tuple_lastelement
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  : extend_tuple f last (lastelement) = last.
Proof.
  unfold extend_tuple.
  assert (H : invweq (weqdnicoprod n lastelement) lastelement = inr tt); [ | now rewrite H].
  apply (invmaponpathsweq (weqdnicoprod n lastelement)).
  exact (homotweqinvweq _ _).
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
