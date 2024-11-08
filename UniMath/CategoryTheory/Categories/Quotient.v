(* We define quotients of categories under a congruence relation on morphism
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.

Local Open Scope cat.

Definition mor_cong_rel (C : category) : UU
  := ∑ (eq : ∏ (x y : C), eqrel (x --> y)),
     ∏ (x y z : C)
       (f f' : x --> y)
       (g g' : y --> z),
     eq _ _ f f'
     → eq _ _ g g'
     → eq _ _ (f · g) (f' · g').

Definition make_mor_cong_rel
           {C : category}
           (eq : ∏ (x y : C), eqrel (x --> y))
           (eqc : ∏ (x y z : C)
                    (f f' : x --> y)
                    (g g' : y --> z),
                  eq _ _ f f'
                  → eq _ _ g g'
                  → eq _ _ (f · g) (f' · g'))
  : mor_cong_rel C
  := eq ,, eqc.

Definition mor_cong_rel_to_eqrel
           {C : category}
           (eq : mor_cong_rel C)
           {x y : C}
           (f g : x --> y)
  : hProp
  := pr1 eq x y f g.

Notation "f ~_{ eq } g" := (mor_cong_rel_to_eqrel eq f g) (at level 70) : cat.

Proposition mor_cong_rel_congruence
            {C : category}
            {eq : mor_cong_rel C}
            {x y z : C}
            {f f' : x --> y}
            {g g' : y --> z}
            (p : f ~_{eq} f')
            (q : g ~_{eq} g')
  : f · g ~_{eq} f' · g'.
Proof.
  exact (pr2 eq _ _ _ _ _ _ _ p q).
Qed.

Section QuotientMorphisms.
  Context {C : category}
          (eq : mor_cong_rel C).

  Definition mor_quot_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, setquot (λ (f g : x --> y), f ~_{ eq } g)).
  Defined.

  Definition mor_quot_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact mor_quot_precategory_ob_mor.
    - exact (λ x, setquotpr _ (identity x)).
    - intros x y z.
      use setquotfun2'.
      + exact (λ f g, f · g).
      + unfold iscomprelrelfun2' ; cbn.
        split.
        * abstract
            (intros f f' g p ;
             use (mor_cong_rel_congruence p) ;
             apply eqrelrefl).
        * abstract
            (intros f g g' q ;
             use (mor_cong_rel_congruence _ q) ;
             apply eqrelrefl).
  Defined.

  Proposition is_precategory_mor_quot
    : is_precategory mor_quot_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros x y.
      use setquotunivprop'.
      + intro.
        apply isasetsetquot.
      + intro f.
        cbn.
        rewrite id_left.
        reflexivity.
    - intros x y.
      use setquotunivprop'.
      + intro.
        apply isasetsetquot.
      + intro f. 
        cbn.
        rewrite id_right.
        reflexivity.
    - intros w x y z.
      use setquotunivprop'.
      {
        intro.
        use impred ; intro.
        use impred ; intro.
        apply isasetsetquot.
      }
      intro f.
      use setquotunivprop'.
      {
        intro.
        use impred ; intro.
        apply isasetsetquot.
      }
      intro g.
      use setquotunivprop'.
      {
        intro.
        apply isasetsetquot.
      }
      intro h.
      cbn.
      rewrite assoc.
      reflexivity.
  Qed.

  Definition mor_quot_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact mor_quot_precategory_data.
    - exact is_precategory_mor_quot.
  Defined.

  Proposition has_homsets_mor_quot_category
    : has_homsets mor_quot_precategory.
  Proof.
    intros x y.
    apply isasetsetquot.
  Qed.

  Definition mor_quot_category
    : category.
  Proof.
    use make_category.
    - exact mor_quot_precategory.
    - exact has_homsets_mor_quot_category.
  Defined.

End QuotientMorphisms.