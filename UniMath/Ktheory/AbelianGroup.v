(* -*- coding: utf-8 -*- *)

(** * abelian groups *)

Require Import UniMath.Algebra.Monoids_and_Groups
               UniMath.NumberSystems.Integers
               UniMath.Ktheory.Tactics
               UniMath.Ktheory.Utilities
               UniMath.CategoryTheory.functor_categories
               UniMath.Ktheory.Representation
               UniMath.Ktheory.Precategories.
Require UniMath.Ktheory.Group.
Unset Automatic Introduction.
Local Open Scope cat.

Delimit Scope abgr with abgr.
Local Open Scope abgr.

Notation Hom_abgr := monoidfun.
Notation "0" := (unel _) : abgr.
Notation "x + y" := ( op x y ) : abgr.
Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, left associativity, only parsing) : abgr.

Definition zeroAbgr : abgr.
  exists Group.zero. split. exact (pr2 Group.zero). intros x y. reflexivity.
Defined.

Definition Z : abgr := hzaddabgr.

Definition commax (G:abgr) := pr2 (pr2 G).

Definition unitproperty {G H:abgr} (p:Hom_abgr G H) : p (unel G) = unel H
  := pr2 (pr2 p).

Definition addproperty {G H:abgr} (p:Hom_abgr G H) (g g':G) : p(g + g') = p g + p g'
  := pr1 (pr2 p) g g'.

(** * abelian groups by generators and relations

      This code is derived from the code in the module [Monoid.Presentation].
      Reduce the duplication later, if possible. *)

Module Presentation.
  Inductive word X : Type :=
    | word_unit : word X
    | word_gen : X -> word X
    | word_inv : word X -> word X
    | word_op : word X -> word X -> word X.
  Arguments word_unit {X}.
  Arguments word_gen {X} x.
  Arguments word_inv {X} w.
  Arguments word_op {X} v w.
  Record reln X := make_reln { lhs : word X; rhs : word X }.
  Arguments lhs {X} r.
  Arguments rhs {X} r.
  Arguments make_reln {X} _ _.
  Record MarkedPreAbelianGroup X :=
    make_preAbelianGroup {
        elem :> Type;
        op0 : elem;
        op1 : X -> elem;
        op_inv : elem -> elem;
        op2 : elem -> elem -> elem }.
  Arguments elem {X} M : rename.
  Arguments op0 {X M} : rename.
  Arguments op1 {X M} x : rename.
  Arguments op_inv {X M} x : rename.
  Arguments op2 {X M} v w : rename.
  Definition wordop X := make_preAbelianGroup X (word X) word_unit word_gen word_inv word_op.
  Fixpoint evalword {X} (Y:MarkedPreAbelianGroup X) (w:word X) : elem Y.
    intros ? Y [|x|w|v w]. { exact op0. } { exact (op1 x). }
    { exact (op_inv (evalword X Y w)). }
    { exact (op2 (evalword X Y v) (evalword X Y w)). } Defined.
  Definition MarkedPreAbelianGroup_to_hrel {X}
             (M:MarkedPreAbelianGroup X) (is:isaset (elem M)) :
      hrel (word X) :=
    λ v w, (evalword M v = evalword M w) ,, is _ _.

  (** eta expansion principle for words *)

  Fixpoint reassemble {X I} (R:I->reln X) (v:wordop X) : evalword (wordop X) v = v.
  Proof. intros ? ? ? [|x|w|v w]. { reflexivity. } { reflexivity. }
         { exact (ap word_inv (reassemble _ _ R w)). }
         { exact (aptwice word_op (reassemble _ _ R v) (reassemble _ _ R w)). } Qed.

  (** ** adequate relations over R *)

  Record AdequateRelation {X I} (R:I->reln X) (r : hrel (word X)) :=
    make_AdequateRelation {
        base: ∏ i, r (lhs (R i)) (rhs (R i));
        reflex : ∏ w, r w w;
        symm : ∏ v w, r v w -> r w v;
        trans : ∏ u v w, r u v -> r v w -> r u w;
        left_compat : ∏ u v w, r v w -> r (word_op u v) (word_op u w);
        right_compat: ∏ u v w, r u v -> r (word_op u w) (word_op v w);
        left_unit : ∏ w, r (word_op word_unit w) w;
        right_unit : ∏ w, r (word_op w word_unit) w;
        assoc : ∏ u v w, r (word_op (word_op u v) w) (word_op u (word_op v w));
        inverse_compat : ∏ v w, r v w -> r (word_inv v) (word_inv w);
        left_inverse : ∏ w, r (word_op (word_inv w) w) word_unit;
        right_inverse: ∏ w, r (word_op w (word_inv w)) word_unit;
        comm : ∏ v w, r (word_op v w) (word_op w v)
      }.
  Arguments make_AdequateRelation {X I} R r _ _ _ _ _ _ _ _ _ _ _ _ _.
  Arguments base {X I R r} _ _.
  Definition adequacy_to_eqrel {X I} (R:I->reln X) (r : hrel (word X)) :
    AdequateRelation R r -> eqrel (word X).
  Proof. intros ? ? ? ? ra. exists r.
         abstract ( split; [ split; [ exact (trans R r ra) | exact (reflex R r ra) ] |
                             exact (symm R r ra)]). Defined.

  (** ** the smallest adequate relation over R
         It is defined as the intersection of all the adequate relations.
         Later we'll have to deal with the "resizing" to resolve issues
         withe universes. *)

  Definition smallestAdequateRelation0 {X I} (R:I->reln X) : hrel (word X).
    intros ? ? ? v w.
    exists (∏ r: hrel (word X), AdequateRelation R r -> r v w).
    abstract (apply impred; intro r; apply impred_prop).
  Defined.
  Lemma adequacy {X I} (R:I->reln X) :
    AdequateRelation R (smallestAdequateRelation0 R).
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _ _ _ _).
         { intros ? r ra. apply base. exact ra. }
         { intros ? r ra. apply (reflex R). exact ra. }
         { intros ? ? p r ra. apply (symm R). exact ra. exact (p r ra). }
         { exact (λ u v w p q r ra, trans R r ra u v w (p r ra) (q r ra)). }
         { intros ? ? ? p r ra. apply (left_compat R). exact ra. exact (p r ra). }
         { intros ? ? ? p r ra. apply (right_compat R). exact ra. exact (p r ra). }
         { intros ? r ra. apply (left_unit R). exact ra. }
         { intros ? r ra. apply (right_unit R). exact ra. }
         { exact (λ u v w r ra, assoc R r ra u v w). }
         { exact (λ v w p r ra, inverse_compat R r ra v w (p r ra)). }
         { exact (λ w r ra, left_inverse R r ra w). }
         { exact (λ w r ra, right_inverse R r ra w). }
         { exact (λ v w r ra, comm R r ra v w). }
  Qed.
  Definition smallestAdequateRelation {X I} (R:I->reln X) : eqrel (word X).
    intros. exact (adequacy_to_eqrel R _ (adequacy R)). Defined.

  (** *** the underlying set of the abelian group with generators X and relations R *)

  Definition universalMarkedPreAbelianGroup0 {X I} (R:I->reln X) : hSet :=
    setquotinset (smallestAdequateRelation R).
  Lemma op_inv_compatibility {X I} (R:I->reln X) :
    iscomprelrelfun (smallestAdequateRelation R) (smallestAdequateRelation R) word_inv.
  Proof. intros. intros v w p r ra. exact (inverse_compat R r ra v w (p r ra)). Qed.
  Lemma op2_compatibility {X I} (R:I->reln X) :
    QuotientSet.iscomprelrelfun2
      (smallestAdequateRelation R) (smallestAdequateRelation R) (smallestAdequateRelation R)
      word_op.
  Proof. intros. split.
    { intros x x' y p r ra. exact (right_compat R r ra x x' y (p r ra)). }
    { intros x y y' p r ra. exact ( left_compat R r ra x y y' (p r ra)). } Qed.

  (** *** the multiplication on on it *)

  Definition univ_inverse {X I} (R:I->reln X) :
      universalMarkedPreAbelianGroup0 R -> universalMarkedPreAbelianGroup0 R.
    intros ? ? ?.  refine (setquotfun _ _ word_inv _). apply op_inv_compatibility. Defined.
  Definition univ_binop {X I} (R:I->reln X) : binop (universalMarkedPreAbelianGroup0 R).
    intros. refine (QuotientSet.setquotfun2 word_op _). apply op2_compatibility. Defined.
  Definition univ_setwithbinop {X I} (R:I->reln X) : setwithbinop
             := setwithbinoppair (universalMarkedPreAbelianGroup0 R) (univ_binop R).

  (** *** the universal pre-Abelian group *)

  Definition universalMarkedPreAbelianGroup {X I} (R:I->reln X) : MarkedPreAbelianGroup X.
    intros. refine (make_preAbelianGroup X (universalMarkedPreAbelianGroup0 R) _ _ _ _).
    { exact (setquotpr _ word_unit). }
    { exact (λ x, setquotpr _ (word_gen x)). }
    { exact (univ_inverse _). }
    { exact (univ_binop _). } Defined.

  (** *** identities for the universal preabelian group *)

  Lemma lift {X I} (R:I->reln X) : issurjective (setquotpr (smallestAdequateRelation R)).
  Proof. intros. exact (issurjsetquotpr (smallestAdequateRelation R)). Qed.
  Lemma is_left_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreAbelianGroup0 R) :
    ((univ_binop _) (setquotpr _ word_unit) w) = w.
  Proof. intros ? ? ? w'. apply isaprop_goal; intro ig. (* was: isaprop_goal ig. *) { apply setproperty. }
    apply (squash_to_prop (lift R w') ig); intros [w []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _
                           (λ r ra, left_unit R r ra w)). Qed.
  Lemma is_right_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreAbelianGroup0 R) :
    ((univ_binop _) w (setquotpr _ word_unit)) = w.
  Proof. intros ? ? ? w'. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R w') ig); intros [w []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _
                           (λ r ra, right_unit R r ra w)). Qed.
  Lemma isassoc_univ_binop {X I} (R:I->reln X) : isassoc(univ_binop R).
  Proof. intros. set (e := smallestAdequateRelation R). intros u' v' w'.
         isaprop_goal ig. { apply setproperty. }
         apply (squash_to_prop (lift R u') ig); intros [u i]; destruct i.
         apply (squash_to_prop (lift R v') ig); intros [v j]; destruct j.
         apply (squash_to_prop (lift R w') ig); intros [w []].
         exact (iscompsetquotpr e _ _ (λ r ra, assoc R r ra u v w)). Qed.
  Lemma is_left_inverse_univ_binop {X I} (R:I->reln X) :
    ∏ w:setquot (smallestAdequateRelation0 R),
      univ_binop R (univ_inverse R w) w =
      setquotpr (smallestAdequateRelation R) word_unit.
  Proof. intros. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R w) ig); intros [v []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _
                           (λ r ra, left_inverse R r ra v)). Qed.
  Lemma is_right_inverse_univ_binop {X I} (R:I->reln X) :
    ∏ w:setquot (smallestAdequateRelation0 R),
      univ_binop R w (univ_inverse R w) =
      setquotpr (smallestAdequateRelation R) word_unit.
  Proof. intros. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R w) ig); intros [v []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _
                           (λ r ra, right_inverse R r ra v)). Qed.
  Lemma iscomm_univ_binop {X I} (R:I->reln X) : iscomm(univ_binop R).
  Proof. intros. set (e := smallestAdequateRelation R). intros v' w'.
         isaprop_goal ig. { apply setproperty. }
         apply (squash_to_prop (lift R v') ig); intros [v j]; destruct j.
         apply (squash_to_prop (lift R w') ig); intros [w []].
         exact (iscompsetquotpr e _ _ (λ r ra, comm R r ra v w)). Qed.
  Fixpoint reassemble_pr {X I} (R:I->reln X) (v:word X) :
    evalword (universalMarkedPreAbelianGroup R) v = setquotpr _ v.
  Proof. intros ? ? ? [|x|w|v w]. { reflexivity. } { reflexivity. }
         { simpl. assert (q := ! reassemble_pr _ _ R w). destruct q. reflexivity. }
         { simpl. assert (p := ! reassemble_pr _ _ R v). destruct p.
                  assert (q := ! reassemble_pr _ _ R w). destruct q.
                  reflexivity. } Qed.
  Lemma pr_eval_compat {X I} (R:I->reln X) (w:word X) :
    setquotpr (smallestAdequateRelation R) (evalword (wordop X) w)
    = evalword (universalMarkedPreAbelianGroup R) w.
  Proof. intros. destruct w as [|x|w|v w]. { reflexivity. } { reflexivity. }
    { exact (ap (setquotpr (smallestAdequateRelation R)) (reassemble R (word_inv w))
           @ !reassemble_pr R (word_inv w)). }
    { assert (p := !reassemble R (word_op v w)). destruct p.
      exact (!reassemble_pr R (word_op v w)). } Qed.

  (** *** abelian groups over X modulo R *)

  Definition toMarkedPreAbelianGroup {X I} (R:I->reln X) (M:abgr) (el:X->M) :
      MarkedPreAbelianGroup X.
    intros. exact {| elem := M; op0 := unel _; op1 := el; op_inv := grinv _; op2 := op |}.
  Defined.
  Record MarkedAbelianGroup {X I} (R:I->reln X) :=
    make_MarkedAbelianGroup {
        m_base :> abgr;
        m_mark : X -> m_base;
        m_reln : ∏ i, evalword (toMarkedPreAbelianGroup R m_base m_mark) (lhs (R i)) =
                           evalword (toMarkedPreAbelianGroup R m_base m_mark) (rhs (R i)) }.
  Arguments make_MarkedAbelianGroup {X I} R _ _ _.
  Arguments m_base {X I R} _.
  Arguments m_mark {X I R} _ x.
  Definition toMarkedPreAbelianGroup' {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : MarkedPreAbelianGroup X :=
    toMarkedPreAbelianGroup R (m_base M) (m_mark M).
  Definition evalwordMM {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : word X -> M :=
    evalword (toMarkedPreAbelianGroup' M).
  Definition MarkedAbelianGroup_to_hrel {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : hrel (word X) :=
    λ v w , eqset (evalwordMM M v) (evalwordMM M w).
  Lemma abelian_group_adequacy {X I} (R:I->reln X) (M:MarkedAbelianGroup R) :
    AdequateRelation R (MarkedAbelianGroup_to_hrel M).
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _ _ _ _).
         { exact (λ i, m_reln R M i). } { reflexivity. }
         { intros ? ?. exact pathsinv0. } { intros ? ? ?. exact pathscomp0. }
         { intros ? ? ? p. simpl in p; simpl.
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros ? ? ? p. simpl in p; simpl.
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros. apply lunax. } { intros. apply runax. } { intros. apply assocax. }
         { intros ? ? p. simpl in p; simpl.
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros. apply grlinvax. } { intros. apply grrinvax. } { intros. apply commax. }
  Qed.
  Record MarkedAbelianGroupMap {X I} {R:I->reln X} (M N:MarkedAbelianGroup R) :=
    make_MarkedAbelianGroupMap {
        map_base :> Hom_abgr M N;
        map_mark : ∏ x, map_base (m_mark M x) = m_mark N x }.
  Arguments map_base {X I R M N} m.
  Arguments map_mark {X I R M N} m x.
  Lemma MarkedAbelianGroupMapEquality {X I} {R:I->reln X} {M N:MarkedAbelianGroup R}
        (f g:MarkedAbelianGroupMap M N) : map_base f = map_base g -> f = g.
  Proof. intros ? ? ? ? ? ? ? j.
         destruct f as [f ft], g as [g gt]; simpl in j. destruct j.
         assert(k : ft = gt). { apply funextsec; intro x. apply setproperty. } destruct k.
         reflexivity. Qed.
  Fixpoint MarkedAbelianGroupMap_compat {X I} {R:I->reln X}
           {M N:MarkedAbelianGroup R} (f:MarkedAbelianGroupMap M N) (w:word X) :
    map_base f (evalwordMM M w) = evalwordMM N w.
  Proof. intros. destruct w as [|x|w|v w].
         { exact (Monoid.unitproperty f). }
         { exact (map_mark f x). }
         { exact (monoidfuninvtoinv f (evalwordMM M w)
                @ ap (grinv N) (MarkedAbelianGroupMap_compat _ _ _ _ _ f w)). }
         { exact (Monoid.multproperty f (evalwordMM M v) (evalwordMM M w)
                  @ aptwice (λ r s, r + s)
                            (MarkedAbelianGroupMap_compat _ _ _ _ _ f v)
                            (MarkedAbelianGroupMap_compat _ _ _ _ _ f w)). } Qed.
  Lemma MarkedAbelianGroupMap_compat2 {X I} {R:I->reln X}
           {M N:MarkedAbelianGroup R} (f g:MarkedAbelianGroupMap M N) (w:word X) :
    map_base f (evalwordMM M w) = map_base g (evalwordMM M w).
  Proof. intros.
         exact (MarkedAbelianGroupMap_compat f w @ !MarkedAbelianGroupMap_compat g w). Qed.

  (** *** the universal marked abelian group over X modulo R *)

  Definition universalMarkedAbelianGroup0 {X I} (R:I->reln X) : abgr.
    intros.
    { exists (univ_setwithbinop R). split.
      { simple refine (_,,_).
        { split.
          { exact (isassoc_univ_binop R). }
          { exists (setquotpr _ word_unit). split.
            { exact (is_left_unit_univ_binop R). }
            { exact (is_right_unit_univ_binop R). } } }
        { simple refine (_,,_).
          { exact (univ_inverse R). }
          { split.
            { exact (is_left_inverse_univ_binop R). }
            { exact (is_right_inverse_univ_binop R). } } } }
      { exact (iscomm_univ_binop R). } }
  Defined.
  Definition universalMarkedAbelianGroup1 {X I} (R:I->reln X) : MarkedPreAbelianGroup X :=
    (toMarkedPreAbelianGroup R
                  (universalMarkedAbelianGroup0 R)
                  (λ x : X, setquotpr (smallestAdequateRelation R) (word_gen x))).
  Lemma universalMarkedAbelianGroup2 {X I} (R:I->reln X) (w:word X) :
    setquotpr (smallestAdequateRelation R) w = evalword (universalMarkedAbelianGroup1 R) w.
  Proof. intros.
    exact (! (ap (setquotpr (smallestAdequateRelation R)) (reassemble R w))
           @ pr_eval_compat R w). Qed.
  Definition universalMarkedAbelianGroup3 {X I} (R:I->reln X) (i:I) :
    evalword (universalMarkedAbelianGroup1 R) (lhs (R i)) =
    evalword (universalMarkedAbelianGroup1 R) (rhs (R i)).
  Proof. intros.
         exact (! universalMarkedAbelianGroup2 R (lhs (R i))
                @ iscompsetquotpr (smallestAdequateRelation R) _ _ (λ r ra, base ra i)
                @ universalMarkedAbelianGroup2 R (rhs (R i))). Qed.
  Definition universalMarkedAbelianGroup {X I} (R:I->reln X) : MarkedAbelianGroup R :=
    make_MarkedAbelianGroup R (universalMarkedAbelianGroup0 R)
                (λ x, setquotpr (smallestAdequateRelation R) (word_gen x))
                (universalMarkedAbelianGroup3 R).
  Fixpoint agreement_on_gens0 {X I} {R:I->reln X} {M:abgr}
        (f g:Hom_abgr (universalMarkedAbelianGroup R) M)
        (p:∏ i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) =
                   g (setquotpr (smallestAdequateRelation R) (word_gen i)))
        (w:word X) :
          pr1 f (setquotpr (smallestAdequateRelation R) w) =
          pr1 g (setquotpr (smallestAdequateRelation R) w).
  Proof. intros. destruct w as [|x|w|v w].
         { intermediate_path (unel M). exact (unitproperty f). exact (!unitproperty g). }
         { apply p. }
         (* compare duplication with the proof of MarkedAbelianGroupMap_compat *)
         { simple refine (monoidfuninvtoinv f (setquotpr (smallestAdequateRelation R) w)
             @ _ @ ! monoidfuninvtoinv g (setquotpr (smallestAdequateRelation R) w)).
           apply (ap (grinv M)). apply agreement_on_gens0. assumption. }
         { simple refine (
               Monoid.multproperty f (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)
             @ _ @ !
               Monoid.multproperty g (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)).
           apply (aptwice (λ r s, r + s)).
           { apply agreement_on_gens0. assumption. }
           { apply agreement_on_gens0. assumption. } } Qed.
  Lemma agreement_on_gens {X I} {R:I->reln X} {M:abgr}
        (f g:Hom_abgr (universalMarkedAbelianGroup R) M) :
        (∏ i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) =
                   g (setquotpr (smallestAdequateRelation R) (word_gen i)))
          -> f = g.
    intros ? ? ? ? ? ? p. apply Monoid.funEquality.
    apply funextsec; intro t; simpl in t.
    apply (surjectionisepitosets _ _ _ (issurjsetquotpr _)).
    { apply setproperty. } { apply agreement_on_gens0. assumption. } Qed.
  Definition universality0 {X I} {R:I->reln X} (M:MarkedAbelianGroup R) :
    universalMarkedAbelianGroup0 R -> M.
  Proof. intros ? ? ? ?.
    apply (setquotuniv _ _ (evalwordMM M)).
    exact (λ _ _ r, r (MarkedAbelianGroup_to_hrel M) (abelian_group_adequacy R M)).
  Defined.
  Definition universality1 {X I} (R:I->reln X)
                           (M:MarkedAbelianGroup R) (v w:universalMarkedAbelianGroup0 R) :
    universality0 M (v + w) = universality0 M v + universality0 M w.
  Proof. intros. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [v' j]; destruct j.
    apply (squash_to_prop (lift R w) ig); intros [w' []].
    reflexivity. Qed.
  Definition universality2 {X I} {R:I->reln X} (M:MarkedAbelianGroup R) :
    monoidfun (universalMarkedAbelianGroup R) M.
  Proof. intros. exists (universality0 M).
      split. { intros v w. apply universality1. } { reflexivity. } Defined.

  (** * universality of the universal marked abelian group *)

  Local Arguments pr1monoidfun {X Y} f x.
  Theorem iscontrMarkedAbelianGroupMap {X I} {R:I->reln X} (M:MarkedAbelianGroup R) :
        iscontr (MarkedAbelianGroupMap (universalMarkedAbelianGroup R) M).
  Proof. intros.
    assert (g := make_MarkedAbelianGroupMap X I R
                           (universalMarkedAbelianGroup R) M
                           (universality2 M) (λ x, idpath _)).
    exists g. intros f. apply MarkedAbelianGroupMapEquality.
    apply Monoid.funEquality. apply funextsec; intro v.
    isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [w []].
    exact ((ap f (universalMarkedAbelianGroup2 R w))
         @ MarkedAbelianGroupMap_compat2 f g w @ !(ap g (universalMarkedAbelianGroup2 R w))).
  Defined.
End Presentation.
Module Free.
  Import Presentation.
  Definition make (X:Type) := @universalMarkedAbelianGroup X empty fromempty.
End Free.
Definition ZZ := Free.make unit.
Module Product.
  Definition make {I} (G:I->abgr) : abgr.
    intros. exists (pr1 (Group.Product.make G)).
    split. exact (pr2 (Group.Product.make G)).
    intros a b. apply funextsec; intro i. apply commax. Defined.
  Definition Proj {I} (G:I->abgr) (i:I) : Hom_abgr (make G) (G i).
    exact @Group.Product.Proj. Defined.
  Definition Map {I} (G:I->abgr) (T:abgr) (g: ∏ i, Hom_abgr T (G i)) :
    Hom_abgr T (make G).
    exact @Group.Product.Fun. Defined.
  Lemma Eqn {I} (G:I->abgr) (T:abgr) (g: ∏ i, Hom_abgr T (G i))
           : ∏ i, Proj G i ∘ Map G T g = g i.
    exact @Group.Product.Eqn. Qed.
  Definition UniqueMap {I} (G:I->abgr) (T:abgr) (h h' : Hom_abgr T (make G)) :
       (∏ i, Proj G i ∘ h = Proj G i ∘ h') -> h = h'.
    intros ? ? ? ? ? e. apply Monoid.funEquality.
    apply funextsec; intro t. apply funextsec; intro i.
    exact (eqtohomot (ap pr1 (e i)) t). Qed.
End Product.
Module Sum.                   (* coproducts *)
  Import Presentation.
  Definition X {I} (G:I->abgr) := total2 G. (* the generators *)
  Inductive J {I} (G:I->abgr) : Type := (* index set for the relations *)
    | J_zero : I -> J G                 (* (i,0) ~  ; redundant relation *)
    | J_sum : (∑ i, G i × G i) -> J G.  (* (i,g)+(i,h) ~ (i,g+h) *)
  Definition R {I} (G:I->abgr) : J G -> reln (X G).
    intros ? ? [i|[i [g h]]].
    { exact (make_reln (word_gen (i,,0)) (word_unit)). }
    { exact (make_reln (word_gen (i,,g+h))
                       (word_op (word_gen (i,,g)) (word_gen (i,,h)))). } Defined.
  Definition make {I} (G:I->abgr) : abgr.
    intros. exact (Presentation.universalMarkedAbelianGroup (R G)). Defined.
  Definition Incl {I} (G:I->abgr) (i:I) : Hom_abgr (G i) (make G).
    intros. simple refine (_,,_).
    { intro g. apply setquotpr. apply word_gen. exact (i,,g). } { split.
      { intros g h. apply iscompsetquotpr. exact (base (adequacy _) (J_sum _ (i,,(g,,h)))). }
      { apply iscompsetquotpr. exact (base (adequacy _) (J_zero _ i)). } } Defined.
  Definition Map0 {I} {G:I->abgr} {T:abgr} (f: ∏ i, Hom_abgr (G i) T) :
      MarkedAbelianGroup (R G).
    intros. simple refine (make_MarkedAbelianGroup (R G) T _ _).
    { intros [i g]. exact (f i g). }
    { intros [i|[i [g h]]].
      { simpl. apply unitproperty. }
      { simpl. apply addproperty. } } Defined.
  Definition Map {I} (G:I->abgr) (T:abgr) (f: ∏ i, Hom_abgr (G i) T) :
      Hom_abgr (make G) T.
    intros. exact (thePoint (iscontrMarkedAbelianGroupMap (Map0 f))). Defined.
  Lemma Eqn {I} (G:I->abgr) (T:abgr) (f: ∏ i, Hom_abgr (G i) T)
           : ∏ i, Map G T f ∘ Incl G i = f i.
    intros. apply Monoid.funEquality. reflexivity. Qed.
  Definition UniqueMap {I} (G:I->abgr) (T:abgr) (h h' : Hom_abgr (make G) T) :
       (∏ i, h ∘ Incl G i = h' ∘ Incl G i) -> h = h'.
    intros ? ? ? ? ? e. apply (agreement_on_gens h h').
    { intros [i g]. exact (ap (evalat g) (ap pr1 (e i))). }
  Qed.
End Sum.
Definition power (I:Type) (X:abgr) : abgr.
  intros. exact (Product.make (λ _:I, Z)). Defined.

(** ** the category of abelian groups *)

Require UniMath.Algebra.Monoids_and_Groups
        UniMath.CategoryTheory.Categories.

Module Category.
  Import UniMath.Algebra.Monoids_and_Groups
         UniMath.CategoryTheory.Categories.

  Definition Ob := abgr.

  Identity Coercion Ob_to_abgr : Ob >-> abgr.

  Definition Mor : Ob -> Ob -> hSet.
    intros G H. exists (monoidfun G H). exact (isasetmonoidfun G H). Defined.

  Definition ObMor : precategory_ob_mor.
  Proof. exists Ob. exact monoidfun. Defined.

  Definition Data : precategory_data.
    exists ObMor. split. intro G. exists (idfun (G : abgr)). split.
    split. reflexivity. intros a b c.  exact monoidfuncomp. Defined.

  Definition MorEquality G H (p q : Mor G H) : pr1 p = pr1 q -> p = q.
    intros. apply Monoid.funEquality. assumption. Qed.

  Definition Precat : category.
    unshelve refine (_,,_).
    { exists Data. split.
      { simpl. split.
        { simpl. intros. apply MorEquality. reflexivity. }
        { intros. apply MorEquality. reflexivity. } }
      { intros. apply MorEquality. reflexivity. } }
    { simpl. intros F G. exact (setproperty (Mor F G)). }
  Defined.

  (** *** products in the category of abelian groups *)

  Module Product.
    Definition make {I} (X:I->ob Precat) : Product X.
      intros. unshelve refine (makeRepresentation _ _).
      - exact (Product.make X).
      - exact (Product.Proj X).
      - intros T. split.
        + intros p. exists (Product.Map X T p).
          apply funextsec; intro i; apply Product.Eqn.
        + intros f f' e. apply Product.UniqueMap.
          intros i. exact (eqtohomot e i).
    Defined.
  End Product.

  (** *** sums (coproducts) in the category of abelian groups *)

  Module Sum.
    Definition make {I} (X:I->ob Precat) : Sum X.
      intros. unshelve refine (makeRepresentation _ _).
      - exact (Sum.make X).
      - exact (Sum.Incl X).
      - intros T. split.
        + intros p. exists (Sum.Map X T p).
          apply funextsec; intro i; apply Sum.Eqn.
        + intros f f' e. apply Sum.UniqueMap.
          intros i. exact (eqtohomot e i).
    Defined.
  End Sum.

  (** *** finite direct sums in the category of abelian groups *)

  Module DirectSum.

  End DirectSum.

End Category.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/AbelianGroup.vo"
End:
*)
