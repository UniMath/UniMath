(**************************************************************************************************

  λ-terms for AlgebraToTheory

  This file contains all the λ-calculus reasoning for the construction of a λ-theory from a
  Λ-algebra (see AlgebraToTheory).

  Contents
  1. The λ-terms for the monoid
  2. The λ-terms for the λ-theory

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.LambdaCalculus.

Local Open Scope vec.

(** * 1. The λ-terms for the monoid *)
Section Monoid.

  Context {lambda : lambda_calculus}.

  Definition compose_λ : lambda 2
  := abs (app
    (var (make_stn 3 0 (idpath true)))
    (app
      (var (make_stn 3 1 (idpath true)))
      (var (make_stn 3 2 (idpath true))))).

  Lemma compose_abs_λ
    (n : nat)
    (a : lambda (S n))
    (b : lambda n)
    : subst
        compose_λ
        (weqvecfun 2 [(abs a ; b)])
      = (abs (subst a (extend_tuple
        (λ i, var (dni_lastelement i))
        (app (inflate b) (var lastelement))))).
  Proof.
    unfold compose_λ.
    rewrite subst_abs.
    do 2 rewrite subst_app.
    do 3 rewrite subst_var.
    extend_tuple_3.
    cbn.
    apply maponpaths.
    rewrite inflate_abs.
    rewrite beta_equality.
    rewrite subst_subst.
    apply maponpaths.
    apply funextfun.
    intro i.
    rewrite <- (homotweqinvweq stnweq i).
    induction (invmap stnweq i);
      refine (maponpaths (λ x, subst (_ x) _) (homotinvweqweq stnweq _) @ !_);
      refine (maponpaths _ (homotinvweqweq stnweq _) @ !_).
    - cbn.
      do 2 rewrite inflate_var.
      rewrite subst_var.
      rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
      now rewrite replace_dni_last.
    - cbn.
      rewrite subst_var.
      now rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
  Qed.

  Lemma compose_assoc_λ
    (n : nat)
    (i j k : stn n)
    : subst compose_λ (weqvecfun 2 [(
        subst compose_λ (weqvecfun 2 [(
          var i ;
          var j
        )]) ;
      var k)])
    = subst compose_λ (weqvecfun 2 [(
        var i ;
        subst compose_λ (weqvecfun 2 [(
          var j ;
          var k
        )])
      )]).
  Proof.
    unfold compose_λ.
    cbn -[weqvecfun].
    refine (maponpaths (λ x, subst _ (weqvecfun _ [(x ; _)])) (subst_abs _ _) @ _).
    refine (compose_abs_λ _ _ _ @ _).
    do 4 rewrite subst_app.
    do 2 rewrite subst_abs.
    do 3 rewrite subst_subst.
    rewrite inflate_var.
    do 3 rewrite subst_var.
    do 4 rewrite subst_app.
    do 6 rewrite subst_var.
    apply maponpaths.
    extend_tuple_3.
    cbn -[weqvecfun v extend_tuple].
    rewrite subst_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 extend_tuple_3.
    cbn.
    do 3 rewrite inflate_var.
    rewrite inflate_abs.
    rewrite beta_equality.
    do 2 rewrite subst_var.
    do 4 rewrite subst_app.
    do 3 rewrite subst_subst.
    do 2 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 3 rewrite subst_var.
    do 2 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 4 rewrite inflate_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    do 2 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    now rewrite replace_dni_last.
  Qed.

  Definition I1_λ : lambda 0
    := abs (var (make_stn 1 0 (idpath true))).

  Lemma compose_I1_abs_λ
    {n : nat}
    (a : lambda (S n))
    : subst compose_λ (weqvecfun _ [(subst I1_λ (weqvecfun _ vnil) ; (abs a))])
    = abs a.
  Proof.
    unfold compose_λ, I1_λ.
    do 2 rewrite subst_abs.
    rewrite subst_var.
    do 2 rewrite subst_app.
    do 3 rewrite subst_var.
    apply maponpaths.
    extend_tuple_3.
    cbn.
    do 2 rewrite inflate_abs.
    do 2 rewrite beta_equality.
    rewrite subst_var.
    rewrite subst_subst.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    refine (_ @ subst_l_var _).
    apply maponpaths.
    apply funextfun.
    intro i.
    rewrite <- (homotweqinvweq stnweq i).
    induction (invmap stnweq i) as [i' | i'];
      refine (maponpaths (λ x, subst (_ x) _) (homotinvweqweq stnweq _) @ _);
      cbn.
    - do 2 rewrite inflate_var.
      rewrite subst_var.
      now rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    - rewrite subst_var.
      now rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
  Qed.

  Lemma compose_I1_abs_0_λ
    (a : lambda 1)
    : subst compose_λ (weqvecfun _ [(I1_λ ; (abs a))])
    = abs a.
  Proof.
    refine (_ @ compose_I1_abs_λ _).
    apply (maponpaths (λ x, _ (_ [(x ; _)]))).
    unfold I1_λ.
    rewrite subst_abs.
    rewrite subst_var.
    now extend_tuple_1.
  Qed.

  Lemma I1_runit_λ
    (a : lambda 1)
    : subst compose_λ (weqvecfun 2 [(
        a ;
        inflate I1_λ
      )])
    = subst compose_λ (weqvecfun 2 [(
        inflate I1_λ ;
        a
      )]).
  Proof.
    unfold compose_λ, I1_λ.
    do 2 refine (subst_abs _ _ @ !_).
    apply maponpaths.
    do 4 rewrite subst_app.
    rewrite inflate_abs.
    do 7 rewrite subst_var.
    extend_tuple_3.
    extend_tuple_3.
    cbn.
    rewrite inflate_abs.
    do 2 rewrite beta_equality.
    rewrite subst_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    now do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
  Qed.

End Monoid.

(** * 2. The λ-terms for the λ-theory *)
Section Theory.

  Context {lambda : lambda_calculus}.

  Definition I2_λ
    : lambda 0
    := abs (abs (app (var (make_stn 2 0 (idpath true))) (var (make_stn 2 1 (idpath true))))).

  Lemma compose_I2_abs_λ
    {n : nat}
    (a : lambda (S (S n)))
    : subst compose_λ (weqvecfun _ [(subst I2_λ (weqvecfun _ vnil) ; abs (abs a))])
    = abs (abs a).
  Proof.
    unfold compose_λ, I2_λ.
    do 3 rewrite subst_abs.
    do 3 rewrite subst_app.
    do 5 rewrite subst_var.
    extend_tuple_3.
    extend_tuple_2.
    extend_tuple_1.
    cbn.
    rewrite inflate_var.
    do 2 rewrite inflate_abs.
    do 2 rewrite beta_equality.
    do 4 rewrite subst_abs.
    do 2 rewrite subst_subst.
    rewrite subst_app.
    do 2 rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    rewrite inflate_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite inflate_abs.
    rewrite beta_equality.
    do 2 rewrite subst_subst.
    do 2 apply maponpaths.
    refine (_ @ subst_l_var _).
    apply maponpaths.
    apply funextfun.
    intro i.
    rewrite <- (homotweqinvweq stnweq i).
    induction (invmap stnweq i) as [i' | i'];
      refine (maponpaths (λ x, subst (subst (_ x) _) _) (homotinvweqweq stnweq _) @ _);
      cbn.
    - rewrite subst_subst.
      unfold inflate.
      rewrite subst_subst.
      rewrite <- (homotweqinvweq stnweq i').
      induction (invmap stnweq i') as [i'' | i''];
        refine (maponpaths (λ x, subst (_ x) _) (homotinvweqweq stnweq _) @ _);
        cbn.
      + do 4 rewrite subst_var.
        do 2 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
        do 2 rewrite subst_var.
        rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
        do 3 rewrite subst_var.
        now rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
      + do 2 rewrite subst_var.
        rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
        rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
        do 2 rewrite subst_var.
        rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
        do 3 rewrite subst_var.
        now rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
            - rewrite subst_subst.
        rewrite subst_var.
        rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
        rewrite subst_var.
        rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
        rewrite subst_var.
        now rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
  Qed.

  Lemma compose_I2_abs_0_λ
    (a : lambda 2)
    : subst compose_λ (weqvecfun _ [(I2_λ ; abs (abs a))])
    = abs (abs a).
  Proof.
    refine (_ @ compose_I2_abs_λ _).
    apply (maponpaths (λ x, _ (_ [(x ; _)]))).
    unfold I2_λ.
    do 2 rewrite subst_abs.
    rewrite subst_app.
    do 2 rewrite subst_var.
    extend_tuple_2.
    cbn.
    now rewrite inflate_var.
  Qed.

  Definition compose_2_λ
    : lambda 3
    := abs (app
      (app
        (var (make_stn 4 0 (idpath true)))
        (app
          (var (make_stn 4 1 (idpath true)))
          (var (make_stn 4 3 (idpath true)))))
      (app
        (var (make_stn 4 2 (idpath true)))
        (var (make_stn 4 3 (idpath true))))).

  Lemma compose_compose_2_λ
    {n : nat}
    (a b c d : stn n)
    : subst compose_λ (weqvecfun _ [(
        subst compose_2_λ (weqvecfun _ [(var a ; var b ; var c)]) ;
        var d
      )])
    = subst compose_2_λ (weqvecfun _ [(
        var a ;
        subst compose_λ (weqvecfun _ [(var b ; var d)]) ;
        subst compose_λ (weqvecfun _ [(var c ; var d)])
      )]).
  Proof.
    unfold compose_λ, compose_2_λ.
    rewrite (subst_abs (m := 3)).
    refine (compose_abs_λ _ _ _ @ _).
    do 8 rewrite subst_app.
    do 3 rewrite subst_abs.
    do 4 rewrite subst_subst.
    rewrite inflate_var.
    do 4 rewrite subst_var.
    do 8 rewrite subst_app.
    do 10 rewrite subst_var.
    do 2 extend_tuple_4.
    do 2 extend_tuple_3.
    cbn.
    rewrite subst_var.
    do 4 rewrite inflate_var.
    do 2 rewrite inflate_abs.
    do 2 rewrite beta_equality.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    do 8 rewrite subst_app.
    do 4 rewrite subst_subst.
    do 3 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 4 rewrite subst_var.
    do 3 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 6 rewrite inflate_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    do 3 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    now rewrite replace_dni_last.
  Qed.

  Lemma compose_2_compose_λ
    {n : nat}
    (a b c d : stn n)
    : subst compose_2_λ
      (weqvecfun 3 [(subst compose_λ (weqvecfun 2 [(var a; var b)]); var c; var d)])
    = subst compose_2_λ
      (weqvecfun 3 [(var a; subst compose_λ (weqvecfun 2 [(var b; var c)]); var d)]).
  Proof.
    unfold compose_2_λ, compose_λ.
    do 4 rewrite subst_abs.
    do 12 rewrite subst_app.
    do 14 rewrite subst_var.
    do 2 extend_tuple_4.
    do 2 extend_tuple_3.
    cbn.
    do 4 rewrite inflate_var.
    do 2 rewrite inflate_abs.
    do 2 rewrite beta_equality.
    do 8 rewrite subst_app.
    do 6 rewrite subst_subst.
    do 6 rewrite subst_var.
    do 3 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    do 6 rewrite inflate_var.
    do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 4 rewrite subst_var.
    now do 4 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
  Qed.

  Definition T_λ
    : lambda 0
    := abs (app
      (var (make_stn 1 0 (idpath true)))
      (abs (abs (var (make_stn 3 1 (idpath true)))))).

  Definition F_λ
    : lambda 0
    := abs (app
      (var (make_stn 1 0 (idpath true)))
      (abs (abs (var (make_stn 3 2 (idpath true)))))).

  Definition term_1_λ
    : lambda 1
    := abs (abs (app
      (var (make_stn 3 0 (idpath true)))
      (abs (app
        (app
          (var (make_stn 4 3 (idpath true)))
          (var (make_stn 4 1 (idpath true))))
        (var (make_stn 4 2 (idpath true))))))).

  Lemma term_1_compose_2_λ
    : subst term_1_λ
      (weqvecfun 1
        [(subst compose_2_λ
            (weqvecfun 3
                [(subst compose_λ (weqvecfun 2 [(subst I2_λ (weqvecfun 0 [()]); (var (make_stn 1 0 (idpath true))))]);
                subst (T_λ) (weqvecfun 0 [()]);
                subst (F_λ) (weqvecfun 0 [()]))]))]) =
    subst compose_λ (weqvecfun 2 [(subst I2_λ (weqvecfun 0 [()]); (var (make_stn 1 0 (idpath true))))]).
  Proof.
    unfold term_1_λ, compose_2_λ.
    do 3 rewrite subst_abs.
    do 5 rewrite subst_app.
    rewrite subst_abs.
    do 5 rewrite subst_var.
    do 2 rewrite subst_app.
    do 3 rewrite subst_var.
    extend_tuple_4.
    extend_tuple_4_1.
    extend_tuple_4_2.
    extend_tuple_4_3.
    extend_tuple_3.
    extend_tuple_2.
    set (a := weqvecfun 2 [(_ ; _)]).
    cbn -[a].
    unfold inflate.
    do 3 rewrite subst_var.
    do 2 rewrite subst_abs.
    do 4 rewrite subst_subst.
    rewrite beta_equality.
    do 8 rewrite subst_app.
    do 7 rewrite subst_subst.
    rewrite subst_var.
    rewrite subst_subst.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite (iscontr_uniqueness (iscontr_empty_tuple (lambda 3)) _).
    unfold compose_λ.
    do 2 rewrite subst_abs.
    rewrite beta_equality.
    do 6 rewrite subst_app.
    do 3 rewrite subst_subst.
    do 6 rewrite subst_var.
    extend_tuple_3.
    extend_tuple_3.
    cbn.
    do 3 rewrite subst_var.
    do 3 rewrite subst_subst.
    rewrite inflate_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite inflate_var.
    rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite inflate_var.
    rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite inflate_var.
    rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    unfold inflate.
    do 3 rewrite subst_subst.
    rewrite (iscontr_uniqueness (iscontr_empty_tuple (lambda 3)) _).
    unfold I2_λ.
    do 4 rewrite subst_abs.
    do 2 rewrite beta_equality.
    do 2 rewrite subst_app.
    do 2 rewrite subst_abs.
    rewrite beta_equality.
    do 4 rewrite subst_var.
    do 3 rewrite subst_app.
    do 2 rewrite subst_subst.
    extend_tuple_2.
    extend_tuple_1.
    unfold inflate.
    do 3 rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 4 rewrite subst_app.
    do 2 rewrite subst_abs.
    do 4 rewrite subst_subst.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    do 2 rewrite subst_app.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 3 rewrite subst_var.
    do 2 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 2 rewrite inflate_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    do 4 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 2 rewrite inflate_var.
    rewrite (iscontr_uniqueness (iscontr_empty_tuple (lambda 3)) _).
    unfold T_λ, F_λ.
    do 2 rewrite subst_abs.
    do 2 rewrite beta_equality.
    do 4 rewrite subst_app.
    do 8 rewrite subst_abs.
    do 4 rewrite subst_subst.
    do 4 rewrite subst_var.
    extend_tuple_3_1.
    extend_tuple_3_2.
    extend_tuple_2.
    extend_tuple_1.
    extend_tuple_1.
    extend_tuple_1.
    cbn.
    do 5 rewrite subst_var.
    rewrite inflate_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 4 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    rewrite subst_app.
    do 2 rewrite beta_equality.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    do 4 rewrite subst_app.
    rewrite inflate_var.
    do 6 rewrite subst_var.
    do 4 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite beta_equality.
    do 2 rewrite subst_abs.
    do 2 rewrite beta_equality.
    do 2 rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    rewrite inflate_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    now rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
  Qed.

  Definition term_2_λ
    : lambda 2
    := (abs (abs (app
      (app
        (var (make_stn 4 3 (idpath true)))
        (app
          (var (make_stn 4 0 (idpath true)))
          (var (make_stn 4 2 (idpath true)))))
      (app
        (var (make_stn 4 1 (idpath true)))
        (var (make_stn 4 2 (idpath true))))))).

  Lemma compose_2_term_1_λ
    : subst compose_2_λ (weqvecfun 3 [(
        subst term_1_λ (weqvecfun 1 [(
          var (make_stn 3 0 (idpath true))
        )]);
        var (make_stn 3 1 (idpath true));
        var (make_stn 3 2 (idpath true))
      )])
    = subst compose_λ (weqvecfun 2 [(
        var (make_stn 3 0 (idpath true));
        subst term_2_λ (weqvecfun 2 [(
          var (make_stn 3 1 (idpath true));
          var (make_stn 3 2 (idpath true))
        )])
      )]).
  Proof.
    unfold term_2_λ, compose_2_λ, compose_λ, term_1_λ.
    do 6 rewrite subst_abs.
    do 11 rewrite subst_app.
    rewrite subst_abs.
    do 12 rewrite subst_var.
    do 2 rewrite subst_app.
    do 3 rewrite subst_var.
    extend_tuple_4.
    extend_tuple_4.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_2.
    extend_tuple_4_1.
    extend_tuple_4_2.
    extend_tuple_4_3.
    extend_tuple_3.
    cbn.
    do 9 rewrite inflate_var.
    do 2 rewrite inflate_abs.
    do 2 rewrite beta_equality.
    do 4 rewrite subst_abs.
    do 2 rewrite subst_subst.
    rewrite beta_equality.
    do 6 rewrite subst_app.
    do 2 rewrite subst_abs.
    do 2 rewrite subst_subst.
    do 5 rewrite subst_var.
    do 2 rewrite subst_app.
    rewrite subst_subst.
    do 7 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 4 rewrite subst_var.
    do 10 rewrite inflate_var.
    do 3 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 4 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 6 rewrite subst_var.
    rewrite inflate_var.
    do 7 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 3 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 5 rewrite inflate_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    do 2 rewrite inflate_app.
    do 2 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_app.
    do 4 rewrite inflate_var.
    rewrite inflate_app.
    do 2 rewrite subst_var.
    do 2 rewrite inflate_var.
    do 4 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    now do 2 rewrite inflate_var.
  Qed.

  Lemma compose_T_λ
    : subst compose_λ (weqvecfun 2 [(
        subst T_λ (weqvecfun 0 [()]);
        subst term_2_λ (weqvecfun 2 [(
          (var (make_stn 2 0 (idpath true)));
          (var (make_stn 2 1 (idpath true)))
        )])
      )])
    = subst compose_λ (weqvecfun 2 [(
        subst I1_λ (weqvecfun 0 [()]);
        (var (make_stn 2 0 (idpath true)))
      )]).
  Proof.
    unfold T_λ, term_2_λ, compose_λ, I1_λ.
    do 6 rewrite subst_abs.
    rewrite subst_var.
    do 9 rewrite subst_app.
    do 2 rewrite subst_abs.
    do 12 rewrite subst_var.
    extend_tuple_4.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3_1.
    extend_tuple_2_1.
    extend_tuple_1.
    cbn.
    do 6 rewrite inflate_var.
    do 3 rewrite inflate_abs.
    do 3 rewrite beta_equality.
    rewrite subst_var.
    do 2 rewrite subst_app.
    do 6 rewrite subst_abs.
    do 3 rewrite subst_subst.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    do 4 rewrite subst_app.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 3 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 5 rewrite subst_var.
    rewrite inflate_var.
    do 5 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 3 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 2 rewrite subst_var.
    do 7 rewrite inflate_var.
    rewrite beta_equality.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 2 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    do 4 rewrite subst_app.
    rewrite inflate_var.
    do 5 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 3 rewrite inflate_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    rewrite beta_equality.
    do 3 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite subst_abs.
    rewrite beta_equality.
    rewrite subst_var.
    rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite inflate_app.
    rewrite subst_app.
    do 2 rewrite inflate_var.
    do 2 rewrite subst_var.
    now do 2 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
  Qed.

  Lemma compose_F_λ
    : subst compose_λ (weqvecfun 2 [(
        subst F_λ (weqvecfun 0 [()]);
        subst term_2_λ (weqvecfun 2 [(
          (var (make_stn 2 0 (idpath true)));
          (var (make_stn 2 1 (idpath true)))
        )])
      )])
    = subst compose_λ (weqvecfun 2 [(
        subst I1_λ (weqvecfun 0 [()]);
        (var (make_stn 2 1 (idpath true)))
      )]).
  Proof.
    unfold F_λ, term_2_λ, compose_λ, I1_λ.
    do 6 rewrite subst_abs.
    rewrite subst_var.
    do 9 rewrite subst_app.
    do 2 rewrite subst_abs.
    do 12 rewrite subst_var.
    extend_tuple_4.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3_2.
    extend_tuple_1.
    cbn.
    do 5 rewrite inflate_var.
    do 3 rewrite inflate_abs.
    do 3 rewrite beta_equality.
    rewrite subst_var.
    do 2 rewrite subst_app.
    do 6 rewrite subst_abs.
    do 3 rewrite subst_subst.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    do 4 rewrite subst_app.
    do 3 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 6 rewrite subst_var.
    do 5 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    do 4 rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 7 rewrite inflate_var.
    rewrite beta_equality.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    do 4 rewrite subst_app.
    do 5 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    do 3 rewrite inflate_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    do 3 rewrite subst_var.
    rewrite beta_equality.
    do 3 rewrite (extend_tuple_inl _ _ _ : extend_tuple _ _ (dni lastelement _) = _).
    rewrite subst_abs.
    rewrite beta_equality.
    rewrite subst_var.
    rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
    rewrite subst_var.
    now rewrite (extend_tuple_inr _ _ : extend_tuple _ _ lastelement = _).
  Qed.

End Theory.
