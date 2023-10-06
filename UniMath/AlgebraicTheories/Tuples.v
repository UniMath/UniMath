Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Lemma stn_eq
  {n : nat}
  (i i' : stn n)
  (H : pr1 i = pr1 i')
  : i = i'.
Proof.
  use subtypePath.
  - intro.
    apply isasetbool.
  - exact H.
Qed.

Definition eqstnweq
  {n n' : nat}
  (H : n = n')
  : stn n ≃ stn n'.
Proof.
  use weq_iso.
  - intro i.
    refine (make_stn _ i _).
    abstract exact (transportf (λ x, i < x) H (stnlt i)).
  - intro i.
    refine (make_stn _ i _).
    abstract exact (transportf (λ x, i < x) (!H) (stnlt i)).
  - abstract (intro i; now apply stn_eq).
  - abstract (intro i; now apply stn_eq).
Defined.

Definition stnweq {n : nat}
  : stn n ⨿ unit ≃ stn (1 + n)
  := weqdnicoprod _ lastelement.

Definition extend_tuple
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  : stn (S n) → T.
Proof.
  intro i.
  induction (invmap stnweq i) as [a | ].
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
  induction (invmap stnweq i) as [a | ].
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
  refine (maponpaths _ (_ : invmap stnweq (i ,, Hi1) = inl (make_stn _ i Hi2))).
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
  refine (maponpaths _ (_ : invmap stnweq i = inr tt)).
  apply (invmaponpathsweq (weqdnicoprod n lastelement)).
  refine (homotweqinvweq _ _ @ _).
  apply subtypePairEquality.
  - intro.
    apply isasetbool.
  - apply Hi.
Qed.

Lemma extend_tuple_inl
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  (i : stn n)
  : extend_tuple f last (stnweq (inl i)) = f i.
Proof.
  exact (maponpaths _ (homotinvweqweq _ (inl i))).
Qed.

Lemma extend_tuple_inr
  {T : UU}
  {n : nat}
  (f : stn n → T)
  (last : T)
  : extend_tuple f last (stnweq (inr tt)) = last.
Proof.
  exact (maponpaths _ (homotinvweqweq _ _)).
Qed.

Lemma extend_tuple_eq
  {T : UU}
  {n : nat}
  {last : T}
  {f : stn n → T}
  {g : stn (S n) → T}
  (Hf : ∏ i, f i = g (stnweq (inl i)))
  (Hlast : last = g (stnweq (inr tt)))
  : extend_tuple f last = g.
Proof.
  apply funextfun.
  intro i.
  unfold extend_tuple.
  refine (_ @ maponpaths g (homotweqinvweq stnweq i)).
  induction (invmap stnweq i).
  - exact (Hf a).
  - exact Hlast.
Qed.
