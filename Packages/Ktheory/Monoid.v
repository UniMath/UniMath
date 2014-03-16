(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1b
	       RezkCompletion.auxiliary_lemmas_HoTT
               Ktheory.Utilities.
Require Ktheory.Magma Ktheory.QuotientSet.
Import RezkCompletion.pathnotations.PathNotations Ktheory.Utilities.Notation. 
Local Notation Hom := monoidfun (only parsing).
Local Notation "x * y" := ( op x y ). 
Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, only parsing).
Definition funEquality G H (p q : Hom G H) : pr1 p == pr1 q -> p == q.
  intros ? ? [p i] [q j] v. simpl in v. destruct v.
  destruct (pr1 (isapropismonoidfun p i j)). reflexivity. Qed.
Definition unitproperty {G H} (p:Hom G H) : p (unel G) == unel H 
  := pr2 (pr2 p).
Definition multproperty {G H} (p:Hom G H) (g g':G) : p(g * g') == p g * p g'
  := pr1 (pr2 p) g g'.
Definition zero : monoid.
  exists Magma.zero. split. intros x y z. reflexivity.
  exists tt. split. intros []. reflexivity. intros []. reflexivity.
Defined.
Definition zero_map (A B:monoid) : Hom A B.
  intros. exists (fun _ => unel B).
  { split. - intros x y. apply pathsinv0. apply lunax.
           - reflexivity. } Defined.
Lemma zero_is_initial (A:monoid) : iscontr (Hom zero A).
Proof. intros. exists (zero_map zero A).
       intros [f e]. apply funEquality; simpl.
       apply funextsec. intro t. induction t. exact (pr2 e). Defined.
Lemma zero_is_final (A:monoid) : iscontr (Hom A zero).
Proof. intros. exists (zero_map A zero).
       intros [f e]. apply funEquality; simpl.
       apply funextsec; intro a. induction (f a). reflexivity. Defined.
Inductive word X : Type :=
  | word_unit : word X
  | word_gen : X -> word X 
  | word_op : word X -> word X -> word X.
Arguments word_unit {X}.
Arguments word_gen {X} x.
Arguments word_op {X} v w.
Record reln X := make_reln { lhs : word X; rhs : word X }.
Arguments lhs {X} r.
Arguments rhs {X} r.
Arguments make_reln {X} _ _.

(** * monoids by generators and relations *)

Module Presentation.

  (** ** premonoids over X
         A pre-monoid over X modulo an adequate relation over R will be a
         monoid M equipped with a map X -> M that respects the relations R. *)

  Inductive word X : Type :=
    | word_unit : word X
    | word_gen : X -> word X 
    | word_op : word X -> word X -> word X.
  Arguments word_unit {X}.
  Arguments word_gen {X} x.
  Arguments word_op {X} v w.
  Record reln X := make_reln { lhs : word X; rhs : word X }.
  Arguments lhs {X} r.
  Arguments rhs {X} r.
  Arguments make_reln {X} _ _.
  Record MarkedPreMonoid X := 
    make_preMonoid {
        elem :> Type;
        op0 : elem;
        op1 : X -> elem;
        op2 : elem -> elem -> elem }.
  Arguments elem {X} M : rename.
  Arguments op0 {X M} : rename.
  Arguments op1 {X M} x : rename.
  Arguments op2 {X M} v w : rename.
  Definition wordop X := make_preMonoid X (word X) word_unit word_gen word_op.
  Fixpoint evalword {X} (Y:MarkedPreMonoid X) (w:word X) : elem Y.
    intros ? Y [|x|v w]. { exact op0. } { exact (op1 x). }
    { exact (op2 (evalword X Y v) (evalword X Y w)). } Defined.
  Definition MarkedPreMonoid_to_hrel {X} 
             (M:MarkedPreMonoid X) (is:isaset (elem M)) : 
      hrel (word X) :=
    fun v w => (evalword M v == evalword M w) ,, is _ _.

  (** eta expansion principle for words *)

  Fixpoint reassemble {X I} (R:I->reln X) (v:wordop X) : evalword (wordop X) v == v.
  Proof. intros ? ? ? [|x|v w]. { reflexivity. } { reflexivity. }
         { exact (aptwice word_op (reassemble _ _ R v) (reassemble _ _ R w)). } Qed.

  (** ** adequate relations over R *)

  Record AdequateRelation {X I} (R:I->reln X) (r : hrel (word X)) := 
    make_AdequateRelation {
        base: forall i, r (lhs (R i)) (rhs (R i));
        reflex : forall w, r w w;
        symm : forall v w, r v w -> r w v;
        trans : forall u v w, r u v -> r v w -> r u w;
        left_compat : forall u v w, r v w -> r (word_op u v) (word_op u w);
        right_compat: forall u v w, r u v -> r (word_op u w) (word_op v w);
        left_unit : forall w, r (word_op word_unit w) w;
        right_unit : forall w, r (word_op w word_unit) w;
        assoc : forall u v w, r (word_op (word_op u v) w) (word_op u (word_op v w))
      }.
  Arguments make_AdequateRelation {X I} R r _ _ _ _ _ _ _ _ _.
  Arguments base {X I R r} _ _.
  Definition adequacy_to_eqrel {X I} (R:I->reln X) (r : hrel (word X)) :
    AdequateRelation R r -> eqrel (word X).
  Proof. intros ? ? ? ? ra. exists r.
         abstract ( split; [ split; [ exact (trans R r ra) | exact (reflex R r ra) ] |
                             exact (symm R r ra)]). Defined.

  (** ** the smallest adequate relation over R 
         It is defined as the intersection of all the adequate relations.
         Later we'll have to deal with the "resizing" to resolve issues
         with universes. *)

  Definition smallestAdequateRelation0 {X I} (R:I->reln X) : hrel (word X).
    intros ? ? ? v w.
    exists (forall r: hrel (word X), AdequateRelation R r -> r v w).
    abstract (apply impred; intro r; apply impred; intros _; apply propproperty).
  Defined.
  Lemma adequacy {X I} (R:I->reln X) : 
    AdequateRelation R (smallestAdequateRelation0 R).
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _).
         { intros ? r ra. apply base. exact ra. }
         { intros ? r ra. apply (reflex R). exact ra. }
         { intros ? ? p r ra. apply (symm R). exact ra. exact (p r ra). }
         { exact (fun u v w p q r ra => trans R r ra u v w (p r ra) (q r ra)). }
         { intros ? ? ? p r ra. apply (left_compat R). exact ra. exact (p r ra). }
         { intros ? ? ? p r ra. apply (right_compat R). exact ra. exact (p r ra). }
         { intros ? r ra. apply (left_unit R). exact ra. }
         { intros ? r ra. apply (right_unit R). exact ra. }
         { exact (fun u v w r ra => assoc R r ra u v w). } 
  Qed.
  Definition smallestAdequateRelation {X I} (R:I->reln X) : eqrel (word X).
    intros. exact (adequacy_to_eqrel R _ (adequacy R)). Defined.

  (** *** the underlying set of the abelian group with generators X and relations R *)

  Definition universalMarkedPreMonoid0 {X I} (R:I->reln X) : hSet := 
    setquotinset (smallestAdequateRelation R).
  Lemma op2_compatibility {X I} (R:I->reln X) : 
    QuotientSet.iscomprelrelfun2
      (smallestAdequateRelation R) (smallestAdequateRelation R) (smallestAdequateRelation R)
      word_op.    
  Proof. intros. split.
    { intros x x' y p r ra. exact (right_compat R r ra x x' y (p r ra)). }
    { intros x y y' p r ra. exact ( left_compat R r ra x y y' (p r ra)). } Qed.

  (** *** the multiplication on on it *)

  Definition univ_binop {X I} (R:I->reln X) : binop (universalMarkedPreMonoid0 R).
    intros. refine (QuotientSet.setquotfun2 word_op _). apply op2_compatibility. Defined.
  Definition univ_setwithbinop {X I} (R:I->reln X) : setwithbinop
             := setwithbinoppair (universalMarkedPreMonoid0 R) (univ_binop R).

  (** *** the universal pre-monoid *)

  Definition universalMarkedPreMonoid {X I} (R:I->reln X) : MarkedPreMonoid X.
    intros. refine (make_preMonoid X (universalMarkedPreMonoid0 R) _ _ _).
    { exact (setquotpr _ word_unit). }
    { exact (fun x => setquotpr _ (word_gen x)). }
    { exact (univ_binop _). } Defined.

  (** *** identities for the universal preabelian group *)

  Lemma lift {X I} (R:I->reln X) : issurjective (setquotpr (smallestAdequateRelation R)).
  Proof. intros. exact (issurjsetquotpr (smallestAdequateRelation R)). Qed.
  Lemma is_left_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreMonoid0 R) :
    ((univ_binop _) (setquotpr _ word_unit) w) == w.
  Proof. intros ? ? ? w'. isaprop_goal ig. { apply setproperty. } 
    apply (squash_to_prop (lift R w') ig); intros [w []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                           (fun r ra => left_unit R r ra w)). Qed.
  Lemma is_right_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreMonoid0 R) :
    ((univ_binop _) w (setquotpr _ word_unit)) == w.
  Proof. intros ? ? ? w'. isaprop_goal ig. { apply setproperty. } 
    apply (squash_to_prop (lift R w') ig); intros [w []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                           (fun r ra => right_unit R r ra w)). Qed.
  Lemma isassoc_univ_binop {X I} (R:I->reln X) : isassoc(univ_binop R).
  Proof. intros. set (e := smallestAdequateRelation R). intros u' v' w'. 
         isaprop_goal ig. { apply setproperty. } 
         apply (squash_to_prop (lift R u') ig); intros [u i]; destruct i.
         apply (squash_to_prop (lift R v') ig); intros [v j]; destruct j.
         apply (squash_to_prop (lift R w') ig); intros [w []].
         exact (iscompsetquotpr e _ _ (fun r ra => assoc R r ra u v w)). Qed.
  Fixpoint reassemble_pr {X I} (R:I->reln X) (v:word X) : 
    evalword (universalMarkedPreMonoid R) v == setquotpr _ v.
  Proof. intros ? ? ? [|x|v w]. { reflexivity. } { reflexivity. }
         { simpl. assert (p := ! reassemble_pr _ _ R v). destruct p.
                  assert (q := ! reassemble_pr _ _ R w). destruct q.
                  reflexivity. } Qed.
  Lemma pr_eval_compat {X I} (R:I->reln X) (w:word X) :
    setquotpr (smallestAdequateRelation R) (evalword (wordop X) w) 
    == evalword (universalMarkedPreMonoid R) w.
  Proof. intros. destruct w as [|x|v w]. { reflexivity. } { reflexivity. } 
    { assert (p := !reassemble R (word_op v w)). destruct p. 
      exact (!reassemble_pr R (word_op v w)). } Qed.

  (** *** abelian groups over X modulo R *)

  Definition toMarkedPreMonoid {X I} (R:I->reln X) (M:monoid) (el:X->M) : 
      MarkedPreMonoid X.
    intros. exact {| elem := M; op0 := unel _; op1 := el; op2 := op |}.
  Defined.
  Record MarkedMonoid {X I} (R:I->reln X) := 
    make_MarkedMonoid {
        m_base :> monoid;
        m_mark : X -> m_base;
        m_reln : forall i, evalword (toMarkedPreMonoid R m_base m_mark) (lhs (R i)) ==
                           evalword (toMarkedPreMonoid R m_base m_mark) (rhs (R i)) }.
  Arguments make_MarkedMonoid {X I} R _ _ _.
  Arguments m_base {X I R} _.
  Arguments m_mark {X I R} _ x.
  Definition toMarkedPreMonoid' {X I} {R:I->reln X} (M:MarkedMonoid R) : MarkedPreMonoid X :=
    toMarkedPreMonoid R (m_base M) (m_mark M).
  Definition evalwordMM {X I} {R:I->reln X} (M:MarkedMonoid R) : word X -> M :=
    evalword (toMarkedPreMonoid' M).
  Definition MarkedMonoid_to_hrel {X I} {R:I->reln X} (M:MarkedMonoid R) : hrel (word X) :=
    fun v w  => eqset (evalwordMM M v) (evalwordMM M w).
  Lemma abelian_group_adequacy {X I} (R:I->reln X) (M:MarkedMonoid R) :
    AdequateRelation R (MarkedMonoid_to_hrel M).
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _).
         { exact (fun i => m_reln R M i). } { reflexivity. }
         { intros ? ?. exact pathsinv0. } { intros ? ? ?. exact pathscomp0. }
         { intros ? ? ? p. simpl in p; simpl. 
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros ? ? ? p. simpl in p; simpl. 
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros. apply lunax. } { intros. apply runax. } { intros. apply assocax. } 
  Qed.
  Record MarkedMonoidMap {X I} {R:I->reln X} (M N:MarkedMonoid R) :=
    make_MarkedMonoidMap {
        map_base :> Hom M N;
        map_mark : forall x, map_base (m_mark M x) == m_mark N x }.
  Arguments map_base {X I R M N} m.
  Arguments map_mark {X I R M N} m x.
  Lemma MarkedMonoidMapEquality {X I} {R:I->reln X} {M N:MarkedMonoid R}
        (f g:MarkedMonoidMap M N) : map_base f == map_base g -> f == g.
  Proof. intros ? ? ? ? ? ? ? j.
         destruct f as [f ft], g as [g gt]; simpl in j. destruct j.
         assert(k : ft == gt). { apply funextsec; intro x. apply setproperty. } destruct k. 
         reflexivity. Qed.
  Fixpoint MarkedMonoidMap_compat {X I} {R:I->reln X}
           {M N:MarkedMonoid R} (f:MarkedMonoidMap M N) (w:word X) :
    map_base f (evalwordMM M w) == evalwordMM N w.
  Proof. intros. destruct w as [|x|v w].
         { exact (unitproperty f). }
         { exact (map_mark f x). }
         { exact (multproperty f (evalwordMM M v) (evalwordMM M w)
                  @ aptwice (fun r s => r * s) 
                            (MarkedMonoidMap_compat _ _ _ _ _ f v) 
                            (MarkedMonoidMap_compat _ _ _ _ _ f w)). } Qed.
  Lemma MarkedMonoidMap_compat2 {X I} {R:I->reln X} 
           {M N:MarkedMonoid R} (f g:MarkedMonoidMap M N) (w:word X) :
    map_base f (evalwordMM M w) == map_base g (evalwordMM M w).
  Proof. intros. 
         exact (MarkedMonoidMap_compat f w @ !MarkedMonoidMap_compat g w). Qed.

  (** *** the universal marked abelian group over X modulo R *)

  Definition universalMarkedMonoid0 {X I} (R:I->reln X) : monoid.
    intros. 
    { exists (univ_setwithbinop R). 
        { split.
          { exact (isassoc_univ_binop R). }
          { exists (setquotpr _ word_unit). split. 
            { exact (is_left_unit_univ_binop R). }
            { exact (is_right_unit_univ_binop R). } } } }
Defined.
  Definition universalMarkedMonoid1 {X I} (R:I->reln X) : MarkedPreMonoid X :=
    (toMarkedPreMonoid R 
                  (universalMarkedMonoid0 R)
                  (fun x : X => setquotpr (smallestAdequateRelation R) (word_gen x))). 
  Lemma universalMarkedMonoid2 {X I} (R:I->reln X) (w:word X) : 
    setquotpr (smallestAdequateRelation R) w == evalword (universalMarkedMonoid1 R) w.
  Proof. intros.
    exact (! (ap (setquotpr (smallestAdequateRelation R)) (reassemble R w))
           @ pr_eval_compat R w). Qed.
  Definition universalMarkedMonoid3 {X I} (R:I->reln X) (i:I) : 
    evalword (universalMarkedMonoid1 R) (lhs (R i)) ==
    evalword (universalMarkedMonoid1 R) (rhs (R i)).
  Proof. intros.
         exact (! universalMarkedMonoid2 R (lhs (R i))
                @ iscompsetquotpr (smallestAdequateRelation R) _ _ (fun r ra => base ra i)
                @ universalMarkedMonoid2 R (rhs (R i))). Qed.
  Definition universalMarkedMonoid {X I} (R:I->reln X) : MarkedMonoid R :=
    make_MarkedMonoid R (universalMarkedMonoid0 R) 
                (fun x => setquotpr (smallestAdequateRelation R) (word_gen x)) 
                (universalMarkedMonoid3 R).
  Fixpoint agreement_on_gens0 {X I} {R:I->reln X} {M:monoid}
        (f g:Hom (universalMarkedMonoid R) M)
        (p:forall i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) ==
                   g (setquotpr (smallestAdequateRelation R) (word_gen i)))
        (w:word X) :
          pr1 f (setquotpr (smallestAdequateRelation R) w) ==
          pr1 g (setquotpr (smallestAdequateRelation R) w).
  Proof. intros. destruct w as [|x|v w].
         { intermediate_path (unel M). exact (unitproperty f). exact (!unitproperty g). }
         { apply p. }
         (* compare duplication with the proof of MarkedMonoidMap_compat *)
         { refine (
               multproperty f (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)
             @ _ @ !
               multproperty g (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)).
           apply (aptwice (fun r s => r * s)).
           { apply agreement_on_gens0. assumption. }
           { apply agreement_on_gens0. assumption. } } Qed.
  Lemma agreement_on_gens {X I} {R:I->reln X} {M:monoid}
        (f g:Hom (universalMarkedMonoid R) M) :
        (forall i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) ==
                   g (setquotpr (smallestAdequateRelation R) (word_gen i))) 
          -> f == g.
    intros ? ? ? ? ? ? p. apply funEquality.
    apply funextsec; intro t; simpl in t. 
    apply (surjectionisepitosets _ _ _ (issurjsetquotpr _)).
    { apply setproperty. } { apply agreement_on_gens0. assumption. } Qed.
  Definition universality0 {X I} {R:I->reln X} (M:MarkedMonoid R) : 
    universalMarkedMonoid0 R -> M.
  Proof. intros ? ? ? ?. 
    apply (setquotuniv _ _ (evalwordMM M)).
    exact (fun _ _ r => r (MarkedMonoid_to_hrel M) (abelian_group_adequacy R M)).
  Defined.
  Definition universality1 {X I} (R:I->reln X) 
                           (M:MarkedMonoid R) (v w:universalMarkedMonoid0 R) :
    universality0 M (v * w) == universality0 M v * universality0 M w.
  Proof. intros. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [v' j]; destruct j.
    apply (squash_to_prop (lift R w) ig); intros [w' []].
    reflexivity. Qed.
  Definition universality2 {X I} {R:I->reln X} (M:MarkedMonoid R) : 
    monoidfun (universalMarkedMonoid R) M.
  Proof. intros. exists (universality0 M).
      split. { intros v w. apply universality1. } { reflexivity. } Defined.

  (** * universality of the universal marked abelian group *)

  Local Arguments pr1monoidfun {X Y} f x.
  Theorem iscontrMarkedMonoidMap {X I} {R:I->reln X} (M:MarkedMonoid R) :
        iscontr (MarkedMonoidMap (universalMarkedMonoid R) M).
  Proof. intros. 
    assert (g := make_MarkedMonoidMap X I R 
                           (universalMarkedMonoid R) M 
                           (universality2 M) (fun x => idpath _)).
    exists g. intros f. apply MarkedMonoidMapEquality.
    apply funEquality. apply funextsec; intro v.
    isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [w []].
    exact ((ap f (universalMarkedMonoid2 R w)) 
         @ MarkedMonoidMap_compat2 f g w @ !(ap g (universalMarkedMonoid2 R w))).
  Defined.
End Presentation.
Module Free.
  Import Presentation.
  Definition make (X:Type) := @universalMarkedMonoid X empty fromempty.
End Free.
Definition NN := Free.make unit.
Module Product.
  Definition make {I} (X:I->monoid) : monoid.
    intros. exists (Magma.Product.make X). split.
    intros a b c. apply funextsec; intro. apply assocax.
    exists (fun i => unel (X i)). split.
    intros a. apply funextsec; intro. apply lunax.
    intros a. apply funextsec; intro. apply runax. Defined.
  Definition Proj {I} (X:I->monoid) (i:I) : Hom (make X) (X i).
    intros. exists (pr1 (Magma.Product.Proj X i)). split. 
    exact (pr2 (Magma.Product.Proj X i)). simpl. reflexivity. Defined.
  Definition Fun {I} (X:I->monoid) (T:monoid) (g: forall i, Hom T (X i))
             : Hom T (make X).
    intros.  exists (pr1 (Magma.Product.Fun X T g)). 
    exists (pr2 (Magma.Product.Fun X T g)). apply funextsec; intro i.
    exact (pr2 (pr2 (g i))). Defined.
  Definition Eqn {I} (X:I->monoid) (T:monoid) (g: forall i, Hom T (X i))
             : forall i, Proj X i ∘ Fun X T g == g i.
    intros. apply funEquality. reflexivity. Qed.
  Lemma issurjective_projection {I} (X:I->monoid) (i:I) :
    isdeceq I -> issurjective (Proj X i).

  (** Reminder: by [isasetifdeceq], I is a set, too.
      We should strengthen this lemma by assuming [isaset I] instead of
      [isdeceq I]. *)

  Proof. intros ? ? ? decide_equality xi. apply hinhpr. 
    refine (_,,_).
    { intro j. destruct (decide_equality i j) as [p|_].
      { exact (transportf X p xi). }
      { exact (unel (X j)). } }
    simpl. destruct (decide_equality i i) as [q|r]; simpl.
    { assert (e : idpath i == q).
      { apply equality_proof_irrelevance'. apply isasetifdeceq. assumption. }
      destruct e. reflexivity. }
    { destruct (r (idpath i)). } Qed.
  Lemma issurjective_projection' {I} (X:I->monoid) (i:I) :
    LEM -> isaset I -> issurjective (Proj X i).
  Proof. intros ? ? ? lem is. apply issurjective_projection.
    apply LEM_for_sets. assumption. assumption. Qed.
End Product.

