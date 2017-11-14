(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013

Extended by: Anders Mörtberg, 2016

************************************************************)


(** **********************************************************

Contents :

- Definition of adjunction
- Construction of an adjunction from some partial data (Theorem 2 (iv) of Chapter IV.1 of
      MacLane)
- Post-composition with a left adjoint is a left adjoint ([is_left_adjoint_post_composition_functor])

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** * Adjunctions *)
Section adjunctions.

Definition adjunction_data (A B : precategory) : UU
  := ∑ (F : functor A B) (G : functor B A),
     nat_trans (functor_identity A) (F ∙ G) ×
               nat_trans (G ∙ F) (functor_identity B).

Definition left_functor {A B} (X : adjunction_data A B) : functor A B
  := pr1 X.

Definition right_functor {A B} (X : adjunction_data A B) : functor B A
  := pr1 (pr2 X).

Definition adjunit {A B} (X : adjunction_data A B)
  : nat_trans (functor_identity _) (_ ∙ _)
  := pr1 (pr2 (pr2 X)).

Definition adjcounit {A B} (X : adjunction_data A B)
  : nat_trans (_ ∙ _ ) (functor_identity _)
  := pr2 (pr2 (pr2 X)).

Definition triangle_1_statement {A B : precategory} (X : adjunction_data A B)
           (F := left_functor X) (η := adjunit X) (ε := adjcounit X)
  : UU
  :=  ∏ a : A, # F (η a) · ε (F a) = identity (F a).

Definition triangle_2_statement {A B : precategory} (X : adjunction_data A B)
           (G := right_functor X) (η := adjunit X) (ε := adjcounit X)
  : UU
  := ∏ b : B, η (G b) · # G (ε b) = identity (G b).

Definition form_adjunction' {A B} (X : adjunction_data A B) : UU
  := triangle_1_statement X × triangle_2_statement X.

Definition form_adjunction {A B : precategory} (F : functor A B) (G : functor B A)
             (eta : nat_trans (functor_identity A) (functor_composite F G))
             (eps : nat_trans (functor_composite G F) (functor_identity B)) : UU :=
  form_adjunction' (F,,G,,eta,,eps).

Definition mk_form_adjunction {A B : precategory} {F : functor A B} {G : functor B A}
           {eta : nat_trans (functor_identity A) (functor_composite F G)}
           {eps : nat_trans (functor_composite G F) (functor_identity B)}
           (H1 : ∏ a : A, # F (eta a) · eps (F a) = identity (F a))
           (H2 : ∏ b : B, eta (G b) · # G (eps b) = identity (G b)) :
  form_adjunction F G eta eps := (H1,,H2).

  Definition are_adjoints {A B : precategory} (F : functor A B) (G : functor B A) : UU :=
    ∑ (etaeps : (nat_trans (functor_identity A) (functor_composite F G))
                  × (nat_trans (functor_composite G F) (functor_identity B))),
    form_adjunction F G (pr1 etaeps) (pr2 etaeps).

  (** Note that this makes the second component opaque for efficiency reasons *)
  Definition mk_are_adjoints {A B : precategory}
             (F : functor A B) (G : functor B A)
             (eta : nat_trans (functor_identity A) (functor_composite F G))
             (eps : nat_trans (functor_composite G F) (functor_identity B))
             (HH : form_adjunction F G eta eps) : are_adjoints F G.
  Proof.
    exists (eta,,eps).
    abstract (exact HH).
  Defined.

  Definition unit_from_are_adjoints {A B : precategory}
             {F : functor A B} {G : functor B A} (H : are_adjoints F G) :
    nat_trans (functor_identity A) (functor_composite F G) := pr1 (pr1 H).

  Definition counit_from_are_adjoints {A B : precategory}
             {F : functor A B} {G : functor B A} (H : are_adjoints F G)  :
    nat_trans (functor_composite G F) (functor_identity B) := pr2 (pr1 H).

  Definition is_left_adjoint {A B : precategory} (F : functor A B) : UU :=
    ∑ (G : functor B A), are_adjoints F G.

Coercion adjunction_data_from_is_left_adjoint {A B : precategory}
         {F : functor A B} (HF : is_left_adjoint F)
  : adjunction_data A B
  := (F,, _ ,,unit_from_are_adjoints (pr2 HF) ,,counit_from_are_adjoints (pr2 HF) ).

  Definition is_right_adjoint {A B : precategory} (G : functor B A) : UU :=
    ∑ (F : functor A B), are_adjoints F G.

  Definition are_adjoints_to_is_left_adjoint {A B : precategory} (F : functor A B) (G : functor B A)
             (H : are_adjoints F G) : is_left_adjoint F := (G,,H).

  Coercion are_adjoints_to_is_left_adjoint : are_adjoints >-> is_left_adjoint.

  Definition are_adjoints_to_is_right_adjoint {A B : precategory} (F : functor A B)
             (G : functor B A) (H : are_adjoints F G) : is_right_adjoint G := (F,,H).

  Coercion are_adjoints_to_is_right_adjoint : are_adjoints >-> is_right_adjoint.

  Definition right_adjoint {A B : precategory}
             {F : functor A B} (H : is_left_adjoint F) : functor B A := pr1 H.

  Lemma is_right_adjoint_right_adjoint {A B : precategory}
        {F : functor A B} (H : is_left_adjoint F) : is_right_adjoint (right_adjoint H).
  Proof.
    exact (F,,pr2 H).
  Defined.

  Definition left_adjoint {A B : precategory}
             {G : functor B A} (H : is_right_adjoint G) : functor A B := pr1 H.

  Lemma is_left_adjoint_left_adjoint {A B : precategory}
        {G : functor B A} (H : is_right_adjoint G) : is_left_adjoint (left_adjoint H).
  Proof.
    exact (G,,pr2 H).
  Defined.

  Definition unit_from_left_adjoint {A B : precategory}
             {F : functor A B}  (H : is_left_adjoint F) :
    nat_trans (functor_identity A) (functor_composite F (right_adjoint H))
    := adjunit H. (* makes use of the coercion above *)

  Definition unit_from_right_adjoint {A B : precategory}
             {G : functor B A}  (H : is_right_adjoint G) :
    nat_trans (functor_identity A) (functor_composite (left_adjoint H) G)
    := unit_from_are_adjoints (pr2 H).

  Definition counit_from_left_adjoint {A B : precategory}
             {F : functor A B}   (H : is_left_adjoint F)  :
    nat_trans (functor_composite (right_adjoint H) F) (functor_identity B)
    := counit_from_are_adjoints (pr2 H).

  Definition counit_from_right_adjoint {A B : precategory}
             {G : functor B A} (H : is_right_adjoint G)  :
    nat_trans (functor_composite G (left_adjoint H)) (functor_identity B)
    := counit_from_are_adjoints (pr2 H).

  Definition triangle_id_left_ad {A B : precategory} {F : functor A B} {G : functor B A}
             (H : are_adjoints F G) :
    ∏ a, # F (unit_from_are_adjoints H a)
           · counit_from_are_adjoints H (F a) = identity (F a) := pr1 (pr2 H).

  Definition triangle_id_right_ad {A B : precategory} {F : functor A B} {G : functor B A}
             (H : are_adjoints F G) :
    ∏ b, unit_from_are_adjoints H (G b) · # G (counit_from_are_adjoints H b) = identity (G b)
    := pr2 (pr2 H).

  Lemma are_adjoints_functor_composite
        {A B C : precategory} {F1 : functor A B} {F2 : functor B C}
        {G1 : functor B A} {G2 : functor C B}
        (H1 : are_adjoints F1 G1) (H2 : are_adjoints F2 G2) :
    are_adjoints (functor_composite F1 F2) (functor_composite G2 G1).
  Proof.
    destruct H1 as [[eta1 eps1] [H11 H12]].
    destruct H2 as [[eta2 eps2] [H21 H22]].
    simpl in *.
    use mk_are_adjoints.
    - apply (nat_trans_comp _ _ _ eta1).
      use (nat_trans_comp _ _ _ _ (nat_trans_functor_assoc_inv _ _ _)).
      apply pre_whisker.
      apply (nat_trans_comp _ _ _ (nat_trans_functor_id_right_inv _)
                            (post_whisker eta2 G1)).
    - use (nat_trans_comp _ _ _ _ eps2).
      apply (nat_trans_comp _ _ _ (nat_trans_functor_assoc _ _ _)).
      apply pre_whisker.
      apply (nat_trans_comp _ _ _ (nat_trans_functor_assoc_inv _ _ _)).
      apply (nat_trans_comp _ _ _ (post_whisker eps1 _)
                            (nat_trans_functor_id_left _)).
    - split; intros a; simpl.
      + rewrite !id_left, !id_right, <-functor_id, <- H11, !functor_comp, <-!assoc.
        apply maponpaths; rewrite assoc.
        etrans; [eapply cancel_postcomposition, pathsinv0, functor_comp|].
        etrans.
        apply cancel_postcomposition, maponpaths.
        apply (nat_trans_ax eps1 (F1 a) (G2 (F2 (F1 a))) (eta2 (F1 a))).
        simpl; rewrite functor_comp, <- assoc.
        etrans; [eapply maponpaths, H21|].
        now apply id_right.
      + rewrite !id_left, !id_right, <- functor_id, <- H22, !functor_comp, assoc.
        apply cancel_postcomposition; rewrite <- assoc.
        etrans; [eapply maponpaths, pathsinv0, functor_comp|].
        etrans.
        eapply maponpaths, maponpaths, pathsinv0.
        apply (nat_trans_ax eta2 (F1 (G1 (G2 a))) (G2 a) (eps1 _)).
        simpl; rewrite functor_comp, assoc.
        etrans; [apply cancel_postcomposition, H12|].
        now apply id_left.
  Defined.

  Lemma is_left_adjoint_functor_composite
        {A B C : precategory} {F1 : functor A B} {F2 : functor B C}
        (H1 : is_left_adjoint F1) (H2 : is_left_adjoint F2) :
    is_left_adjoint (functor_composite F1 F2).
  Proof.
    use tpair.
    - apply (functor_composite (pr1 H2) (pr1 H1)).
    - apply are_adjoints_functor_composite.
      + apply (pr2 H1).
      + apply (pr2 H2).
  Defined.

  Lemma is_left_adjoint_iso {A B : precategory} (hsB : has_homsets B)
        (F G : functor A B) (αiso : @iso [A,B,hsB] F G) (HF : is_left_adjoint F) :
    is_left_adjoint G.
  Proof.
    set (α := pr1 αiso : nat_trans F G).
    set (αinv := inv_from_iso αiso : nat_trans G F).
    destruct HF as [F' [[α' β'] [HF1 HF2]]]; simpl in HF1, HF2.
    use tpair.
    - apply F'.
    - use mk_are_adjoints.
      + apply (nat_trans_comp _ _ _ α' (post_whisker α F')).
      + apply (nat_trans_comp _ _ _ (pre_whisker F' αinv) β').
      + split.
        * unfold triangle_1_statement.
          simpl; intro a; rewrite assoc, functor_comp.
          etrans; [ apply cancel_postcomposition; rewrite <- assoc;
                    apply maponpaths, (nat_trans_ax αinv)|].
          etrans; [ rewrite assoc, <- !assoc;
                    apply maponpaths, maponpaths, (nat_trans_ax β')|].
          simpl; rewrite assoc.
          etrans; [ apply cancel_postcomposition, (nat_trans_ax αinv)|].
          rewrite assoc.
          etrans; [ apply cancel_postcomposition; rewrite <- assoc;
                    apply maponpaths, HF1|].
          now rewrite id_right; apply (nat_trans_eq_pointwise (iso_after_iso_inv αiso)).
        * unfold triangle_2_statement in *.
          simpl; intro b; rewrite functor_comp, assoc.
          etrans; [ apply cancel_postcomposition; rewrite <- assoc;
                    eapply maponpaths, pathsinv0, functor_comp|].
          etrans; [ apply cancel_postcomposition, maponpaths, maponpaths,
                    (nat_trans_eq_pointwise (iso_inv_after_iso αiso))|].
          cbn. rewrite (functor_id F'), id_right. apply (HF2 b).
  Defined.


  (** * Identity functor is a left adjoint *)


  Lemma is_left_adjoint_functor_identity {A : precategory} :
    is_left_adjoint (functor_identity A).
  Proof.
    use tpair.
    + exact (functor_identity A).
    + exists (nat_trans_id _,, nat_trans_id _).
      abstract (now split; [intros a; apply id_left| intros a; apply id_left]).
  Defined.

  (** * Construction of an adjunction from some partial data (Theorem 2 (iv) of Chapter IV.1 of
      MacLane) *)
Section right_adjoint_from_partial.

Definition is_universal_arrow_from {D C : precategory}
           (S : functor D C) (c : C) (r : D) (v : C⟦S r, c⟧) : UU :=
  ∏ (d : D) (f : C⟦S d,c⟧), ∃! (f' : D⟦d,r⟧), f = # S f' · v.

Context {X A : precategory}
        (F : functor X A)
        (G0 : ob A -> ob X)
        (eps : ∏ a, A⟦F (G0 a),a⟧)
        (Huniv : ∏ a, is_universal_arrow_from F a (G0 a) (eps a)).

Local Definition G_data : functor_data A X.
Proof.
  use tpair.
  + apply G0.
  + intros a b f.
    apply (pr1 (pr1 (Huniv b (G0 a) (eps a · f)))).
Defined.

Local Definition G_is_functor : is_functor G_data.
Proof.
  split.
  + intro a; simpl.
    assert (H : eps a · identity a = # F (identity (G0 a)) · eps a).
    { now rewrite functor_id, id_left, id_right. }
    set (H2 := Huniv a (G0 a) (eps a · identity a)).
    apply (pathsinv0 (maponpaths pr1 (pr2 H2 (_,,H)))).
  + intros a b c f g; simpl.
    set (H2 := Huniv c (G0 a) (eps a · (f · g))).
    destruct H2 as [[fac Hfac] p]; simpl.
    set (H1 := Huniv b (G0 a) (eps a · f)).
    destruct H1 as [[fab Hfab] p1]; simpl.
    set (H0 := Huniv c (G0 b) (eps b · g)).
    destruct H0 as [[fbc Hfbc] p2]; simpl.
    assert (H : eps a · (f · g) = # F (fab · fbc) · eps c).
    { now rewrite assoc, Hfab, <- assoc, Hfbc, assoc, <- functor_comp. }
    apply (pathsinv0 (maponpaths pr1 (p (_,,H)))).
Qed.

Local Definition G : functor A X := tpair _ G_data G_is_functor.

Local Definition unit : nat_trans (functor_identity X) (functor_composite F G).
Proof.
  use mk_nat_trans.
  * intro x.
    apply (pr1 (pr1 (Huniv (F x) x (identity _)))).
  *  intros x y f; simpl.
     destruct (Huniv (F y) y (identity (F y))) as [t p], t as [t p0]; simpl.
     destruct (Huniv (F x) x (identity (F x))) as [t0 p1], t0 as [t0 p2]; simpl.
     destruct
       (Huniv (F y) (G0 (F x)) (eps (F x) · # F f)) as [t1 p3], t1 as [t1 p4]; simpl.
     assert (H1 : # F f = # F (t0 · t1) · eps (F y));
     [now rewrite functor_comp, <- assoc, <- p4, assoc, <- p2, id_left|];
     destruct (Huniv (F y) x (# F f)) as [t2 p5];
     set (HH := (maponpaths pr1 (p5 (_,,H1))));
     simpl in HH; rewrite HH.
     assert (H2 : # F f = # F (f · t) · eps (F y));
     [now rewrite functor_comp, <- assoc, <- p0, id_right|];
     set (HHH := (maponpaths pr1 (p5 (_,,H2)))); simpl in HHH;
     now rewrite HHH.
Defined.

Local Definition counit :  nat_trans (functor_composite G F) (functor_identity A).
Proof.
  use tpair.
  * apply eps.
  * abstract (intros a b f; simpl; apply (pathsinv0 (pr2 (pr1 (Huniv b (G0 a) (eps a · f)))))).
Defined.

Local Lemma form_adjunctionFG : form_adjunction F G unit counit.
Proof.
  use tpair; simpl.
  + unfold triangle_1_statement; cbn.
    intros x.
    destruct (Huniv (F x) x (identity (F x))) as [[f hf] H]; simpl.
    apply (!hf).
  + intros a; simpl.
    destruct (Huniv (F (G0 a)) (G0 a) (identity (F (G0 a)))) as [[f hf] H]; simpl.
    destruct ((Huniv a (G0 (F (G0 a))) (eps (F (G0 a)) · eps a))) as [[g hg] Hg]; simpl.
    destruct (Huniv _ _ (eps a)) as [t p].
    assert (H1 : eps a = # F (identity _) · eps a).
    now rewrite functor_id, id_left.
    assert (H2 : eps a = # F (f · g) · eps a).
    now rewrite functor_comp, <- assoc, <- hg, assoc, <- hf, id_left.
    set (HH := maponpaths pr1 (p (_,,H1))); simpl in HH.
    set (HHH := maponpaths pr1 (p (_,,H2))); simpl in HHH.
    now rewrite HHH, <- HH.
Qed.

Definition left_adjoint_from_partial : is_left_adjoint F :=
  (G,, (unit,, counit),, form_adjunctionFG).
Definition right_adjoint_from_partial : is_right_adjoint G :=
  (F,, (unit,, counit),, form_adjunctionFG).

End right_adjoint_from_partial.

  (** * Construction of an adjunction from some partial data

(Theorem 2 (ii) of Chapter IV.1 of  MacLane) *)

Section left_adjoint_from_partial.


Definition is_universal_arrow_to {D C : precategory}
           (S : functor D C) (c : C) (r : D) (v : C⟦c, S r⟧) : UU :=
  ∏ (d : D) (f : C⟦c, S d⟧), ∃! (f' : D⟦r,d⟧), v · #S f' = f.

Context {X A : precategory}
        (G : functor A X)
        (F0 : ob X -> ob A)
        (eta : ∏ x, X⟦x, G (F0 x)⟧)
        (Huniv : ∏ x, is_universal_arrow_to G x (F0 x) (eta x)).

Local Definition F_data : functor_data X A.
Proof.
  use tpair.
  + apply F0.
  + intros a b f.
    use (pr1 (pr1 (Huniv _ _ _ ))). apply (f · eta _ ).
    (* apply (pr1 (pr1 (Huniv b (G0 a) (eps a · f)))). *)
Defined.

Local Definition F_is_functor : is_functor F_data.
Proof.
  split.
  + intro x; simpl.
    apply pathsinv0, path_to_ctr.
    rewrite functor_id, id_left, id_right; apply idpath.
  + intros a b c f g; simpl.
    apply pathsinv0, path_to_ctr.
    rewrite functor_comp, assoc.
    set (H2 := Huniv _ _ (f · eta _ )).
    rewrite (pr2 (pr1 H2)).
    do 2 rewrite <- assoc; apply maponpaths.
    set (H3 := Huniv _ _ (g · eta _ )).
    apply (pr2 (pr1 H3)).
Defined.

Local Definition left_adj_from_partial : functor X A := F_data,, F_is_functor.
Local Notation F := left_adj_from_partial.

Local Definition counit_left_from_partial
  : functor_composite G F ⟹ functor_identity A.
Proof.
  use mk_nat_trans.
  - intro a.
    apply (pr1 (pr1 (Huniv _ _  (identity _)))).
  - intros a b f; simpl.
    destruct (Huniv _ _ (identity (G b))) as [t p], t as [t p0]; simpl.
    destruct (Huniv _ _ (identity (G a))) as [t0 p1], t0 as [t0 p2]; simpl.
    destruct
      (Huniv _ _  (#G f · eta _ )) as [t1 p3], t1 as [t1 p4]; simpl.
    assert (H1 : # G f =  eta _ · # G (t1 · t)  ).
    { rewrite functor_comp. rewrite assoc. rewrite p4.
      rewrite <- assoc. rewrite p0. rewrite id_right; apply idpath. }
    destruct (Huniv _ _  (# G f)) as [t2 p5].
    set (HH := (maponpaths pr1 (p5 (_,,!H1))));
    simpl in HH; rewrite HH.
    assert (H2 : #G f = eta _ · #G (t0 · f)).
    { rewrite functor_comp. rewrite assoc. rewrite p2.
      rewrite id_left; apply idpath. }
    set (HHH := (maponpaths pr1 (p5 (_,,!H2)))); simpl in HHH;
    now rewrite HHH.
Defined.

Local Definition unit_left_from_partial : functor_identity X ⟹ functor_composite F G.
Proof.
  use tpair.
  * apply eta.
  * abstract (intros a b f; simpl; apply (pathsinv0 (pr2 (pr1 (Huniv _ _  (f · eta _ )))))).
Defined.

Local Lemma form_adjunctionFG_left_from_partial
  : form_adjunction F G unit_left_from_partial counit_left_from_partial.
Proof.
  use tpair; simpl.
  + unfold triangle_1_statement; cbn.
    intros x; simpl.
    destruct (Huniv _ _ (identity (G (F0 x)))) as [[f hf] H]; simpl.
    destruct ((Huniv _ _ (*eps (F (G0 a)) · eps a*)
                         (eta _ · eta (G (F0 x))))) as [[g hg] Hg]; simpl.
    destruct (Huniv _ _ (eta x)) as [t p].
    assert (H1 : eta x =  eta x · # G (identity _)).
    { now rewrite functor_id, id_right. }
    assert (H2 : eta x = eta x · # G (g · f) ).
    { rewrite functor_comp.  rewrite assoc. rewrite hg.
      rewrite <- assoc. rewrite hf. now rewrite id_right. }
    set (HH := maponpaths pr1 (p (_,,!H1))); simpl in HH.
    set (HHH := maponpaths pr1 (p (_,,!H2))); simpl in HHH.
    now rewrite HHH, <- HH.
  + unfold triangle_2_statement; cbn.
    intro a.
    destruct (Huniv _ _ (identity (G a))) as [[f hf] H]; simpl.
    apply hf.
Defined.

Definition right_adjoint_left_from_partial : is_right_adjoint G :=
  (F,, (unit_left_from_partial,, counit_left_from_partial),,
    form_adjunctionFG_left_from_partial).

Definition left_adjoint_left_from_partial : is_left_adjoint F :=
  (G,, (unit_left_from_partial,, _),, form_adjunctionFG_left_from_partial).

End left_adjoint_from_partial.


(** * Post-composition with a left adjoint is a left adjoint *)
Section postcomp.

Context {C D E : precategory} (hsD : has_homsets D) (hsE : has_homsets E)
        (F : functor D E) (HF : is_left_adjoint F).

Let G : functor E D := right_adjoint HF.
Let H : are_adjoints F G := pr2 HF.
Let η : nat_trans (functor_identity D) (functor_composite F G):= unit_from_left_adjoint H.
Let ε : nat_trans (functor_composite G F) (functor_identity E) := counit_from_left_adjoint H.
Let H1 : ∏ a : D, # F (η a) · ε (F a) = identity (F a) := triangle_id_left_ad H.
Let H2 : ∏ b : E, η (G b) · # G (ε b) = identity (G b) := triangle_id_right_ad H.

Lemma is_left_adjoint_post_composition_functor :
  is_left_adjoint (post_composition_functor C D E hsD hsE F).
Proof.
  exists (post_composition_functor _ _ _ _ _ G).
  use tpair.
  - split.
    + use mk_nat_trans.
      * simpl; intros F'.
        apply (nat_trans_comp _ _ _
                              (nat_trans_comp _ _ _ (nat_trans_functor_id_right_inv F')
                                              (pre_whisker F' η))
                              (nat_trans_functor_assoc_inv _ _ _)).
      * abstract (intros F1 F2 α; apply (nat_trans_eq hsD); intro c; simpl in *;
                    now rewrite !id_right, !id_left; apply (nat_trans_ax η (F1 c) _ (α c))).
    + use mk_nat_trans.
      * simpl; intros F'.
        apply (nat_trans_comp _ _ _
                              (nat_trans_functor_assoc _ _ _)
                              (nat_trans_comp _ _ _ (pre_whisker F' ε)
                                              (nat_trans_functor_id_left _))).
      * abstract (intros F1 F2 α; apply (nat_trans_eq hsE); intro c; simpl in *;
                    now rewrite !id_right, !id_left; apply (nat_trans_ax ε _ _ (α c))).
  - abstract (split; simpl; intro F';
              [ apply (nat_trans_eq hsE); simpl; intro c;
                now rewrite !id_left, !id_right; apply H1
              | apply (nat_trans_eq hsD); simpl; intro c;
                now rewrite !id_left, !id_right; apply H2]).
Defined.

End postcomp.

End adjunctions.


Section HomSetIso_from_Adjunction.

  Context {C D : precategory} {F : functor C D} {G : functor D C} (H : are_adjoints F G).

  Let η := unit_from_are_adjoints H.
  Let ε := counit_from_are_adjoints H.

  (** * Definition of the maps on hom-types *)

  Definition φ_adj {A : C} {B : D} : F A --> B → A --> G B
    := λ f : F A --> B, η _ · #G f.

  Definition φ_adj_inv {A : C} {B : D} : A --> G B → F A --> B
    := λ g : A --> G B, #F g · ε _ .

  (** * Proof that those maps are inverse to each other *)

  Lemma φ_adj_after_φ_adj_inv {A : C} {B : D} (g : A --> G B)
    : φ_adj (φ_adj_inv g) = g.
  Proof.
    unfold φ_adj.
    unfold φ_adj_inv.
    assert (X':=triangle_id_right_ad H).
    rewrite functor_comp.
    rewrite assoc.
    assert (X2 := nat_trans_ax η). simpl in X2.
    rewrite <- X2; clear X2.
    rewrite <- assoc.
    pathvia (g · identity _).
    - apply maponpaths.
      apply X'.
    - apply id_right.
  Qed.

  Lemma φ_adj_inv_after_φ_adj {A : C} {B : D} (f : F A --> B)
    : φ_adj_inv (φ_adj f) = f.
  Proof.
    unfold φ_adj, φ_adj_inv.
    rewrite functor_comp.
    assert (X2 := nat_trans_ax ε); simpl in *.
    rewrite <- assoc.
    rewrite X2; clear X2.
    rewrite assoc.
    pathvia (identity _ · f).
    - apply cancel_postcomposition.
      apply triangle_id_left_ad.
    - apply id_left.
  Qed.

  Definition adjunction_hom_weq (A : C) (B : D) : F A --> B ≃ A --> G B.
  Proof.
    exists φ_adj.
    apply (gradth _ φ_adj_inv).
    - apply φ_adj_inv_after_φ_adj.
    - apply φ_adj_after_φ_adj_inv.
  Defined.

  (** * Proof of the equations (naturality squares) of the adjunction *)

  Lemma φ_adj_natural_precomp (A : C) (B : D) (f : F A --> B) (X : C) (h : X --> A)
    : φ_adj (#F h · f) = h · φ_adj f.
  Proof.
    unfold φ_adj.
    rewrite functor_comp.
    set (T:=nat_trans_ax η); simpl in T.
    rewrite assoc.
    rewrite <- T.
    apply pathsinv0, assoc.
  Qed.

  Lemma φ_adj_natural_postcomp (A : C) (B : D) (f : F A --> B) (Y : D) (k : B --> Y)
    : φ_adj (f · k) = φ_adj f · #G k.
  Proof.
    unfold φ_adj.
    rewrite <- assoc.
    apply maponpaths.
    apply (functor_comp G).
  Qed.

  Lemma φ_adj_inv_natural_precomp (A : C) (B : D) (g : A --> G B) (X : C) (h : X --> A)
    : φ_adj_inv (h · g) = #F h · φ_adj_inv g.
  Proof.
    unfold φ_adj_inv.
    rewrite functor_comp.
    apply pathsinv0, assoc.
  Qed.

  Lemma φ_adj_inv_natural_postcomp (A : C) (B : D) (g : A --> G B) (Y : D) (k : B --> Y)
    : φ_adj_inv (g · #G k) = φ_adj_inv g · k.
  Proof.
    unfold φ_adj_inv.
    rewrite functor_comp.
    set (T:=nat_trans_ax ε); simpl in T.
    rewrite <- assoc.
    rewrite T.
    apply assoc.
  Qed.

End HomSetIso_from_Adjunction.
