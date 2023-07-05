Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.Tuples.

(** The core datatype *)

(*** The data of the lambda calculus *)

Definition lambda_calculus_data : UU := ∑
  (L : nat → hSet)
  (var : ∏ n, stn n → L n)
  (app : ∏ n, L n → L n → L n)
  (abs : ∏ n, L (S n) → L n),
  (∏
    (A : ∏ n l, UU)
    (f_var : ∏ n i, A _ (var n i))
    (f_app : ∏ n l l', A _ l → A _ l' → A _ (app n l l'))
    (f_abs : ∏ n l, A _ l → A _ (abs n l))
    , (∏ n l, A n l)
  ).

Definition lambda_calculus_data_to_function (L : lambda_calculus_data) : nat → hSet := pr1 L.
Coercion lambda_calculus_data_to_function : lambda_calculus_data >-> Funclass.

Definition var {L : lambda_calculus_data} {n : nat} (i : stn n) : L n := pr12 L n i.
Definition app {L : lambda_calculus_data} {n : nat} (l l' : L n) : L n := pr122 L n l l'.
Definition abs {L : lambda_calculus_data} {n : nat} (l : L (S n)) : L n := pr1 (pr222 L) n l.

Definition lambda_calculus_ind
  {L : lambda_calculus_data}
  (A : ∏ n (l : L n), UU)
  (f_var : ∏ n i, A _ (var i))
  (f_app : ∏ n l l', A _ l → A _ l' → A _ (app l l'))
  (f_abs : ∏ n l, A _ l → A _ (abs l))
  : ∏ n l, A n l
  := pr2 (pr222 L) A f_var f_app f_abs.

(**** Operations derived from the data *)

Definition lambda_calculus_rect
  {L : lambda_calculus_data}
  (A : nat → UU)
  (f_var : ∏ n, stn n → A n)
  (f_app : ∏ n, A n → A n → A n)
  (f_abs : ∏ n, A (S n) → A n)
  : (∏ n, L n → A n)
  := lambda_calculus_ind
    (L := L)
    (λ n _, A n)
    f_var
    (λ n _ _, f_app n)
    (λ n _, f_abs n).

Definition inflate
  {L : lambda_calculus_data}
  {n : nat}
  (l : L n)
  : L (S n)
  := lambda_calculus_rect _ (λ _ i, (var (dni_lastelement i))) (λ _, app) (λ _, abs) n l.

Definition substitute
  {L : lambda_calculus_data}
  {m n : nat}
  (l : L m)
  (targets : stn m → L n)
  : L n
  := lambda_calculus_rect
    (λ _, (∏ n, _ → L n))
    (λ _ i _ targets, targets i)
    (λ _ f g _ targets, app (f _ targets) (g _ targets))
    (λ _ f _ targets, abs (f _ (extend_tuple (T := L _) (λ i, inflate (targets i)) (var lastelement))))
    _ l n targets.

(*** The properties of the lambda calculus *)

Definition ind_var (L : lambda_calculus_data) : UU := ∏ A f_var f_app f_abs n i,
  lambda_calculus_ind (L := L) A f_var f_app f_abs n (var i) = f_var _ i.

Definition ind_app (L : lambda_calculus_data) : UU := ∏ A f_var f_app f_abs n l l',
  lambda_calculus_ind (L := L) A f_var f_app f_abs n (app l l') = f_app _ _ _
    (lambda_calculus_ind _ f_var f_app f_abs _ l)
    (lambda_calculus_ind _ f_var f_app f_abs _ l').

Definition ind_abs (L : lambda_calculus_data) : UU := ∏ A f_var f_app f_abs n l,
  lambda_calculus_ind (L := L) A f_var f_app f_abs n (abs l) = f_abs _ _
    (lambda_calculus_ind _ f_var f_app f_abs _ l).

Definition has_beta (L : lambda_calculus_data) : UU := ∏ n (f : L (S n)) g,
  (app (abs f) g) = substitute f (extend_tuple var g).

Definition has_eta (L : lambda_calculus_data) : UU := ∏ n (f : L n),
  abs (app (inflate f) (var lastelement)) = f.

Definition is_lambda_calculus (L : lambda_calculus_data) : UU :=
  ind_var L ×
  ind_app L ×
  ind_abs L ×
  has_beta L ×
  has_eta L.

(*** The combined datatype of data and properties *)

Definition lambda_calculus : UU := ∑ L, is_lambda_calculus L.

Coercion lambda_calculus_to_lambda_calculus_data (L : lambda_calculus)
  : lambda_calculus_data
  := pr1 L.

Definition lambda_calculus_ind_var
  {L : lambda_calculus}
  {A f_var f_app f_abs n}
  (i : stn n)
  : lambda_calculus_ind (L := L) A f_var f_app f_abs n (var i) = f_var _ i
  := pr12 L A f_var f_app f_abs n i.

Definition lambda_calculus_ind_app
  {L : lambda_calculus}
  {A f_var f_app f_abs n}
  (l l' : L n)
  : lambda_calculus_ind (L := L) A f_var f_app f_abs n (app l l') = f_app _ _ _
    (lambda_calculus_ind _ f_var f_app f_abs _ l)
    (lambda_calculus_ind _ f_var f_app f_abs _ l')
  := pr122 L A f_var f_app f_abs n l l'.

Definition lambda_calculus_ind_abs
  {L : lambda_calculus}
  {A f_var f_app f_abs n}
  (l : L (S n))
  : lambda_calculus_ind (L := L) A f_var f_app f_abs n (abs l) = f_abs _ _
    (lambda_calculus_ind _ f_var f_app f_abs _ l)
  := pr1 (pr222 L) A f_var f_app f_abs n l.

Definition lambda_calculus_has_beta {L : lambda_calculus} {n f g}
  : (app (abs f) g) = substitute f (extend_tuple var g)
  := pr12 (pr222 L) n f g.

Definition lambda_calculus_has_eta {L : lambda_calculus} {n f}
  : abs (app (inflate f) (var lastelement)) = f
  := pr22 (pr222 L) n f.

(**** Derived properties *)

(***** Rect *)
Definition lambda_calculus_rect_var {L : lambda_calculus} {A f_var f_app f_abs n} i
  : lambda_calculus_rect (L := L) A f_var f_app f_abs n (var i) = f_var _ i
  := lambda_calculus_ind_var i.

Definition lambda_calculus_rect_app {L : lambda_calculus} {A f_var f_app f_abs n} l l'
  : lambda_calculus_rect (L := L) A f_var f_app f_abs n (app l l') = f_app _
    (lambda_calculus_rect _ f_var f_app f_abs _ l)
    (lambda_calculus_rect _ f_var f_app f_abs _ l')
  := lambda_calculus_ind_app l l'.

Definition lambda_calculus_rect_abs {L : lambda_calculus} {A f_var f_app f_abs n} l
  : lambda_calculus_rect (L := L) A f_var f_app f_abs n (abs l) = f_abs _
    (lambda_calculus_rect _ f_var f_app f_abs _ l)
  := lambda_calculus_ind_abs l.

(***** Inflate *)
Definition inflate_var {L : lambda_calculus} {n} (i : stn n)
  : inflate (L := L) (var i) = var (dni_lastelement i)
  := lambda_calculus_rect_var i.

Definition inflate_app {L : lambda_calculus} {n} (l l' : L n)
  : inflate (L := L) (app l l') = app (inflate l) (inflate l')
  := lambda_calculus_rect_app l l'.

Definition inflate_abs {L : lambda_calculus} {n} (l : L (S n))
  : inflate (abs l) = abs (inflate l)
  := lambda_calculus_rect_abs l.

(***** Substitute *)
Definition substitute_var {L : lambda_calculus} {m n} (i : stn m) (targets : stn m → L n)
  : substitute (var i) targets = targets i
  := maponpaths (λ x, x _ _) (lambda_calculus_rect_var i).

Definition substitute_app {L : lambda_calculus} {m n} (l l' : L m) (targets : stn m → L n)
  : substitute (app l l') targets = (app (substitute l targets) (substitute l' targets))
  := maponpaths (λ x, x _ _) (lambda_calculus_rect_app l l').

Definition substitute_abs {L : lambda_calculus} {m n} (l : L (S m)) (targets : stn m → L n)
  : substitute (abs l) targets = abs (substitute l (extend_tuple (λ i, inflate (targets i)) (var lastelement)))
  := maponpaths (λ x, x _ _) (lambda_calculus_rect_abs l).
