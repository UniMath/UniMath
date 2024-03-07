(**************************************************************************************************

  The untyped λ-calculus

  Gives an axiomatization of the pure untyped λ-calculus with β-equality and provides related
  definitions and lemmas.
  The untyped λ-calculus can be formalized as an inductive type, and a quotient of that type would
  then give the λ-calculus with β-equality. Alternatively one could formalize it as a higher
  inductive type.
  However, inductive types are frowned upon in the UniMath library and coq does not support higher
  inductive types natively, so instead this file axiomatizes the type of the λ-calculus: it gives a
  description of what such a(n) (inductive) type of the λ-calculus would have, including induction
  principle. It allows one to add (L : lambda_calculus) as a hypothesis to a definition, or as a
  section variable, which then gives access to "the" (or "a") λ-calculus.

  Contents
  1. The data of the λ-calculus [lambda_calculus_data]
  2. Properties and operations derived from the data
  3. A definition of the λ-calculus with compatibility between the pieces of data [lambda_calculus]
  4. Properties derived from the full λ-calculus
  4.1. Properties of rect
  4.2. Properties of subst [subst_l_var]
  4.3. A tactic for reducing λ-terms [reduce_lambda]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.Combinatorics.Tuples.

(** * 1. The data of the λ-calculus *)

Definition lambda_calculus_data : UU := ∑
  (L : nat → hSet)
  (var : ∏ n, stn n → L n)
  (app : ∏ n, L n → L n → L n)
  (abs : ∏ n, L (S n) → L n)
  (subst : ∏ m n, L m → (stn m → L n) → L n)
  (inflate := (λ _ l, subst _ _ l (λ i, (var _ (stnweq (inl i))))) : ∏ n, L n → L (S n))
  (subst_var : ∏ m n i (f : stn m → L n), subst _ _ (var _ i) f = f i)
  (subst_app : ∏ m n l l' (f : stn m → L n),
    subst _ _ (app _ l l') f = app _ (subst _ _ l f) (subst _ _ l' f))
  (subst_abs : ∏ m n l (f : stn m → L n),
    subst _ _ (abs _ l) f
    = abs _ (subst _ _ l (extend_tuple (λ i, inflate _ (f i)) (var _ (stnweq (inr tt))))))
  (subst_subst : ∏ l m n t (g : stn l → L m) (f : stn m → L n),
    subst _ _ (subst _ _ t g) f = subst _ _ t (λ i, subst _ _ (g i) f))
  (beta : ∏ n (f : L (S n)) g,
    app _ (abs _ f) g = subst _ _ f (extend_tuple (var _) g)),
  (∏
    (A : ∏ n l,
      hSet)
    (f_var : ∏ n i,
      A n (var n i))
    (f_app : ∏ n l l',
      A _ l → A _ l' → A _ (app n l l'))
    (f_abs : ∏ n l,
      A _ l → A _ (abs n l))
    (f_subst : ∏ m n l f,
      A _ l → (∏ i, A _ (f i)) → A _ (subst m n l f))
    (f_inflate := (λ n _ al, f_subst _ _ _ _ al (λ i, (f_var _ (stnweq (inl i)))))
      : ∏ n (l : L n), A n l → A (S n) (inflate _ l))
    (f_subst_var : ∏ m n i f af,
      PathOver (Y := A n) (subst_var m n i f) (f_subst _ _ _ _ (f_var _ i) af) (af i))
    (f_subst_app : ∏ m n l al l' al' f af,
      PathOver
        (Y := A n)
        (subst_app m n l l' f)
        (f_subst _ _ _ _ (f_app _ _ _ al al') af)
        (f_app _ _ _ (f_subst _ _ _ _ al af) (f_subst _ _ _ _ al' af)))
    (f_subst_abs : ∏ m n l al f af,
      PathOver
      (Y := A n)
      (subst_abs m n l f)
      (f_subst _ _ _ _ (f_abs _ _ al) af)
      (f_abs _ _ (f_subst _ _ _ _
        al
        (extend_tuple_dep (A := A (S n)) (λ i, f_inflate _ _ (af i)) (f_var _ (stnweq (inr tt)))))))
    (f_subst_subst : ∏ l m n t a g ag f af,
      PathOver
      (Y := A n)
      (subst_subst l m n t g f)
      (f_subst _ _ _ _ (f_subst _ _ _ _ a ag) af)
      (f_subst _ _ _ _ a (λ i, f_subst _ _ _ _ (ag i) af)))
    (f_beta : ∏ n f af g ag,
      PathOver
        (Y := A n)
        (beta n f g)
        (f_app _ _ _ (f_abs _ _ af) ag)
        (f_subst _ _ _ _ af (extend_tuple_dep (A := A n) (f_var _) ag)))
    , (∏ n l, A n l)
  ).

Definition lambda_calculus_data_to_function (L : lambda_calculus_data) : nat → hSet := pr1 L.
Coercion lambda_calculus_data_to_function : lambda_calculus_data >-> Funclass.

Definition var {L : lambda_calculus_data} {n : nat} (i : stn n) : L n := pr12 L n i.
Definition app {L : lambda_calculus_data} {n : nat} (l l' : L n) : L n := pr122 L n l l'.
Definition abs {L : lambda_calculus_data} {n : nat} (l : L (S n)) : L n := pr1 (pr222 L) n l.
Definition subst {L : lambda_calculus_data} {m n : nat} (l : L m) (f : stn m → L n)
  : L n
  := pr12 (pr222 L) m n l f.

Notation "( a b )" := (app a b).
Notation "(π m )" := (var (make_stn _ m (idpath true))).
Notation "(λ' n , x )" := (@abs _ n x).

Definition inflate {L : lambda_calculus_data} {n} (l : L n)
  : L (S n)
  := subst l (λ i, (var (stnweq (inl i)))).
Definition subst_var {L : lambda_calculus_data} {m n} i (f : stn m → L n)
  : subst (var i) f = f i
  := pr122 (pr222 L) m n i f.
Definition subst_app {L : lambda_calculus_data} {m n} l l' (f : stn m → L n)
  : subst (app l l') f = app (subst l f) (subst l' f)
  := pr1 (pr222 (pr222 L)) m n l l' f.
Definition subst_abs {L : lambda_calculus_data} {m n} l (f : stn m → L n)
  : subst (abs l) f = abs (subst l (extend_tuple (λ i, inflate (f i)) (var (stnweq (inr tt)))))
  := pr12 (pr222 (pr222 L)) m n l f.
Definition subst_subst {L : lambda_calculus_data} {l m n} t (g : stn l → L m) (f : stn m → L n)
  : subst (subst t g) f = subst t (λ i, subst (g i) f)
  := pr122 (pr222 (pr222 L)) l m n t g f.
Definition beta_equality {L : lambda_calculus_data} {n} (f : L (S n)) g
  : app (abs f) g = subst f (extend_tuple var g)
  := pr1 (pr222 (pr222 (pr222 L))) n f g.

Definition lambda_calculus_ind
  {L : lambda_calculus_data}
  (A : ∏ n (l : L n),
    hSet)
  (f_var : ∏ n i,
    A n (var i))
  (f_app : ∏ n l l',
    A _ l → A _ l' → A n (app l l'))
  (f_abs : ∏ n l,
    A _ l → A n (abs l))
  (f_subst : ∏ m n l f,
    A m l → (∏ i, A _ (f i)) → A n (subst l f))
  (f_inflate := (λ n _ al, f_subst _ _ _ _ al (λ i, (f_var _ (stnweq (inl i))))) : ∏ n (l : L n),
    A n l → A (S n) (inflate l))
  (f_paths :
    (∏ m n i f af,
      PathOver (Y := A n) (subst_var i f) (f_subst _ _ _ _ (f_var m i) af) (af i)) ×
    (∏ m n l al l' al' f af,
      PathOver
        (Y := A n)
        (subst_app l l' f)
        (f_subst _ _ _ _ (f_app m _ _ al al') af)
        (f_app _ _ _ (f_subst _ _ _ _ al af) (f_subst _ _ _ _ al' af))) ×
    (∏ m n l al f af,
      PathOver
        (Y := A n)
        (subst_abs l f)
        (f_subst _ _ _ _ (f_abs m _ al) af)
        (f_abs _ _ (f_subst _ _ _ _
          al
          (extend_tuple_dep (A := A (S n)) (λ i, f_inflate _ _ (af i)) (f_var _ (stnweq (inr tt))))))) ×
    (∏ l m n t a g ag f af,
      PathOver
        (Y := A n)
        (subst_subst t g f)
        (f_subst m n _ _ (f_subst l m _ _ a ag) af)
        (f_subst _ _ _ _ a (λ i, f_subst _ _ _ _ (ag i) af))) ×
    (∏ n f af g ag,
      PathOver
        (Y := A n)
        (beta_equality f g)
        (f_app _ _ _ (f_abs _ _ af) ag)
        (f_subst _ _ _ _ af (extend_tuple_dep (A := A n) (f_var _) ag)))
  )
  : (∏ n l, A n l)
  := pr2 (pr222 (pr222 (pr222 L)))
    A
    f_var
    f_app
    f_abs
    f_subst
    (pr1 f_paths)
    (pr12 f_paths)
    (pr122 f_paths)
    (pr1 (pr222 f_paths))
    (pr2 (pr222 f_paths)).

(** * 2. Properties and operations derived from the data *)

Definition lambda_calculus_rect
  {L : lambda_calculus_data}
  (A : nat → hSet)
  (f_var : ∏ n, stn n → A n)
  (f_app : ∏ n, A n → A n → A n)
  (f_abs : ∏ n, A (S n) → A n)
  (f_subst : ∏ m n, A m → (stn m → A n) → A n)
  (f_inflate := (λ n a, f_subst _ _ a (λ i, (f_var _ (stnweq (inl i))))) : ∏ n, A n → A (S n))
  (f_paths :
    (∏ m n i af,
      (f_subst m n (f_var m i) af) = (af i)) ×
    (∏ m n al al' af,
      (f_subst m n (f_app _ al al') af) = (f_app _ (f_subst _ _ al af) (f_subst _ _ al' af))) ×
    (∏ m n al af,
      (f_subst m n (f_abs m al) af)
      = (f_abs _ (f_subst _ _ al (extend_tuple (λ i, f_inflate _ (af i)) (f_var _ (stnweq (inr tt))))))) ×
    (∏ l m n a ag af,
      (f_subst m n (f_subst l m a ag) af) = (f_subst _ _ a (λ i, f_subst _ _ (ag i) af))) ×
    (∏ n af ag,
      (f_app n (f_abs _ af) ag) = (f_subst _ _ af (extend_tuple (f_var _) ag)))
  )
  : (∏ n, L n → A n).
Proof.
  use lambda_calculus_ind.
  - exact f_var.
  - exact (λ _ _ _, f_app _).
  - exact (λ _ _, f_abs _).
  - exact (λ _ _ _ _, f_subst _ _).
  - repeat split;
      simpl;
      intros;
      refine (PathOverConstant_map1 _ _).
    + apply f_paths.
    + apply f_paths.
    + refine (pr122 f_paths _ _ _ _ @ _).
      do 2 apply maponpaths.
      symmetry.
      apply extend_tuple_dep_const.
    + apply f_paths.
    + refine ((pr2 (pr222 f_paths)) _ _ _ @ _).
      apply maponpaths.
      symmetry.
      apply extend_tuple_dep_const.
Defined.

Definition lambda_calculus_ind_prop
  {L : lambda_calculus_data}
  (A : ∏ n (l : L n),
    hProp)
  (f_var : ∏ n i,
    A n (var i))
  (f_app : ∏ n l l',
    A _ l → A _ l' → A n (app l l'))
  (f_abs : ∏ n l,
    A _ l → A n (abs l))
  (f_subst : ∏ m n l f,
    A m l → (∏ i, A _ (f i)) → A n (subst l f))
  : (∏ n l, A n l).
Proof.
  use (lambda_calculus_ind (λ n l, hProp_to_hSet (A n l))).
  - exact f_var.
  - exact f_app.
  - exact f_abs.
  - exact f_subst.
  - repeat split;
      simpl;
      intros;
      apply transportf_weq_pathover;
      apply propproperty.
Defined.

Lemma subst_inflate {L : lambda_calculus_data} {m n} (l : L m) (f : stn (S m) → L n)
  : subst (inflate l) f = subst l (λ i, f (stnweq (inl i))).
Proof.
  unfold inflate.
  rewrite subst_subst.
  apply maponpaths.
  apply funextfun.
  intro i.
  now rewrite subst_var.
Qed.

Definition inflate_var {L : lambda_calculus_data} {n} (i : stn n)
  : inflate (L := L) (var i) = var (stnweq (inl i))
  := subst_var i _.

Definition inflate_app {L : lambda_calculus_data} {n} (l l' : L n)
  : inflate (L := L) (app l l') = app (inflate l) (inflate l')
  := subst_app l l' _.

Definition inflate_abs {L : lambda_calculus_data} {n} (l : L (S n))
  : inflate (abs l)
  = abs (subst l (extend_tuple (λ i, inflate (inflate (var i))) (var (stnweq (inr tt))))).
Proof.
  unfold inflate.
  refine (subst_abs l _ @ _).
  do 2 apply maponpaths.
  apply (maponpaths (λ x, _ x _)).
  apply funextfun.
  intro.
  now rewrite inflate_var, subst_var, subst_var.
Qed.

Definition inflate_subst {L : lambda_calculus_data} {m n} (l : L m) (f : stn m → L n)
  : inflate (subst l f) = subst l (λ i, (inflate (f i)))
  := subst_subst l f _.

(** * 3. A definition of the λ-calculus with compatibility between the pieces of data *)

Definition ind_var (L : lambda_calculus_data) : UU := ∏ A f_var f_app f_abs f_subst f_paths n i,
  lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (var i) = f_var _ i.

Definition ind_app (L : lambda_calculus_data) : UU := ∏ A f_var f_app f_abs f_subst f_paths n l l',
  lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (app l l') = f_app _ _ _
    (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l)
    (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l').

Definition ind_abs (L : lambda_calculus_data) : UU := ∏ A f_var f_app f_abs f_subst f_paths n l,
  lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (abs l) = f_abs _ _
    (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l).

Definition ind_subst (L : lambda_calculus_data)
  : UU
  := ∏ A f_var f_app f_abs f_subst f_paths m n l f,
    lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (subst l f) = f_subst m n _ _
      (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l)
      (λ i, lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ (f i)).

Definition is_lambda_calculus (L : lambda_calculus_data) : UU :=
  ind_var L ×
  ind_app L ×
  ind_abs L ×
  ind_subst L.

Definition lambda_calculus : UU := ∑ L, is_lambda_calculus L.

#[reversible=no] Coercion lambda_calculus_to_lambda_calculus_data (L : lambda_calculus)
  : lambda_calculus_data
  := pr1 L.

Definition lambda_calculus_ind_var
  {L : lambda_calculus}
  {A f_var f_app f_abs f_subst f_paths n}
  (i : stn n)
  : lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (var i) = f_var _ i
  := pr12 L A f_var f_app f_abs f_subst f_paths n i.

Definition lambda_calculus_ind_app
  {L : lambda_calculus}
  {A f_var f_app f_abs f_subst f_paths n}
  (l l' : L n)
  : lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (app l l') = f_app _ _ _
    (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l)
    (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l')
  := pr122 L A f_var f_app f_abs f_subst f_paths n l l'.

Definition lambda_calculus_ind_abs
  {L : lambda_calculus}
  {A f_var f_app f_abs f_subst f_paths n}
  (l : L (S n))
  : lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (abs l) = f_abs _ _
    (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l)
  := pr1 (pr222 L) A f_var f_app f_abs f_subst f_paths n l.

Definition lambda_calculus_ind_subst
  {L : lambda_calculus}
  {A f_var f_app f_abs f_subst f_paths m n}
  (l : L m)
  (f : stn m → L n)
  : lambda_calculus_ind (L := L) A f_var f_app f_abs f_subst f_paths n (subst l f) = f_subst _ _ _ _
    (lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ l)
    (λ i, lambda_calculus_ind _ f_var f_app f_abs f_subst f_paths _ (f i))
  := pr2 (pr222 L) A f_var f_app f_abs f_subst f_paths m n l f.

(** * 4. Properties derived from the full λ-calculus *)

(** ** 4.1. Properties of rect *)

Definition lambda_calculus_rect_var {L : lambda_calculus} {A f_var f_app f_abs f_subst f_paths n} i
  : lambda_calculus_rect (L := L) A f_var f_app f_abs f_subst f_paths n (var i) = f_var _ i
  := lambda_calculus_ind_var i.

Definition lambda_calculus_rect_app
  {L : lambda_calculus}
  {A f_var f_app f_abs f_subst f_paths n}
  l
  l'
  : lambda_calculus_rect (L := L) A f_var f_app f_abs f_subst f_paths n (app l l') = f_app _
    (lambda_calculus_rect _ f_var f_app f_abs f_subst f_paths _ l)
    (lambda_calculus_rect _ f_var f_app f_abs f_subst f_paths _ l')
  := lambda_calculus_ind_app l l'.

Definition lambda_calculus_rect_abs {L : lambda_calculus} {A f_var f_app f_abs f_subst f_paths n} l
  : lambda_calculus_rect (L := L) A f_var f_app f_abs f_subst f_paths n (abs l) = f_abs _
    (lambda_calculus_rect _ f_var f_app f_abs f_subst f_paths _ l)
  := lambda_calculus_ind_abs l.

Definition lambda_calculus_rect_subst
  {L : lambda_calculus}
  {A f_var f_app f_abs f_subst f_paths m n}
  l
  f
  : lambda_calculus_rect (L := L) A f_var f_app f_abs f_subst f_paths n (subst l f) = f_subst m n
    (lambda_calculus_rect _ f_var f_app f_abs f_subst f_paths _ l)
    (λ i, lambda_calculus_rect _ f_var f_app f_abs f_subst f_paths _ (f i))
  := lambda_calculus_ind_subst l f.

(** ** 4.2. Properties of subst [subst_l_var] *)

Lemma subst_l_var
  {L : lambda_calculus}
  {n : nat}
  (l : L n)
  : subst l var = l.
Proof.
  use (lambda_calculus_ind_prop (λ n l, (subst l var = l) ,, (setproperty _ _ _)));
    cbn.
  - intros.
    apply subst_var.
  - intros ? ? ? H1 H2.
    now rewrite subst_app, H1, H2.
  - intros ? ? H.
    rewrite subst_abs.
    apply maponpaths.
    refine (_ @ H).
    apply maponpaths.
    apply extend_tuple_eq.
    + intro.
      apply inflate_var.
    + apply idpath.
  - intros ? ? ? ? ? H.
    rewrite subst_subst.
    apply maponpaths.
    apply funextfun.
    intro.
    apply H.
Qed.

(** ** 4.3. A tactic for reducing λ-terms [reduce_lambda] *)

Ltac repeatc n t :=
  (t; repeatc (S n) t) || (
    match n with
    | 0 => idtac
    | 1 => idtac t "."
    | S (S _) => idtac "do" n t "."
    end
  ).

Tactic Notation "repeatc" tactic(t) :=
  repeatc 0 t.

Ltac reduce_lambda := repeat progress (
  (repeatc rewrite subst_var);
  (repeatc rewrite subst_l_var);
  (repeatc rewrite subst_app);
  (repeatc rewrite subst_abs);
  (repeatc rewrite subst_subst);
  (repeatc rewrite subst_inflate);
  (repeatc rewrite inflate_var);
  (repeatc rewrite inflate_app);
  (repeatc rewrite inflate_abs);
  (repeatc rewrite inflate_subst);
  (repeatc rewrite beta_equality);
  (repeatc rewrite extend_tuple_inl);
  (repeatc rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _) );
  (repeatc rewrite extend_tuple_inr);
  (repeatc rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _))
).
