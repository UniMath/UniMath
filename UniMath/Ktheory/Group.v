(* -*- coding: utf-8 -*- *)

Require Import UniMath.Algebra.Monoids_and_Groups
	       UniMath.CategoryTheory.total2_paths
               UniMath.Ktheory.Utilities.
Require UniMath.Ktheory.Monoid.
Unset Automatic Introduction.
Local Notation Hom := monoidfun.
Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, left associativity, only parsing).
Local Notation "x * y" := ( op x y ).
Definition zero : gr.
  exists Monoid.zero. exists (pr2 Monoid.zero). exists (idfun unit).
  split. intro x. reflexivity. intro x. reflexivity. Defined.

(** * groups by generators and relations *)

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
  Record MarkedPreGroup X :=
    make_preGroup {
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
  Definition wordop X := make_preGroup X (word X) word_unit word_gen word_inv word_op.
  Fixpoint evalword {X} (Y:MarkedPreGroup X) (w:word X) : elem Y.
    intros ? Y [|x|w|v w]. { exact op0. } { exact (op1 x). }
    { exact (op_inv (evalword X Y w)). }
    { exact (op2 (evalword X Y v) (evalword X Y w)). } Defined.
  Definition MarkedPreGroup_to_hrel {X}
             (M:MarkedPreGroup X) (is:isaset (elem M)) :
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
        right_inverse: ∏ w, r (word_op w (word_inv w)) word_unit
      }.
  Arguments make_AdequateRelation {X I} R r _ _ _ _ _ _ _ _ _ _ _ _.
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
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _ _ _).
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
  Qed.
  Definition smallestAdequateRelation {X I} (R:I->reln X) : eqrel (word X).
    intros. exact (adequacy_to_eqrel R _ (adequacy R)). Defined.

  (** *** the underlying set of the abelian group with generators X and relations R *)

  Definition universalMarkedPreGroup0 {X I} (R:I->reln X) : hSet :=
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
      universalMarkedPreGroup0 R -> universalMarkedPreGroup0 R.
    intros ? ? ?.  refine (setquotfun _ _ word_inv _). apply op_inv_compatibility. Defined.
  Definition univ_binop {X I} (R:I->reln X) : binop (universalMarkedPreGroup0 R).
    intros. refine (QuotientSet.setquotfun2 word_op _). apply op2_compatibility. Defined.
  Definition univ_setwithbinop {X I} (R:I->reln X) : setwithbinop
             := setwithbinoppair (universalMarkedPreGroup0 R) (univ_binop R).

  (** *** the universal marked pre-group *)

  Definition universalMarkedPreGroup {X I} (R:I->reln X) : MarkedPreGroup X.
    intros. refine (make_preGroup X (universalMarkedPreGroup0 R) _ _ _ _).
    { exact (setquotpr _ word_unit). }
    { exact (λ x, setquotpr _ (word_gen x)). }
    { exact (univ_inverse _). }
    { exact (univ_binop _). } Defined.

  (** *** identities for the universal preabelian group *)

  Lemma lift {X I} (R:I->reln X) : issurjective (setquotpr (smallestAdequateRelation R)).
  Proof. intros. exact (issurjsetquotpr (smallestAdequateRelation R)). Qed.
  Lemma is_left_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreGroup0 R) :
    ((univ_binop _) (setquotpr _ word_unit) w) = w.
  Proof. intros ? ? ? w'. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R w') ig); intros [w []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _
                           (λ r ra, left_unit R r ra w)). Qed.
  Lemma is_right_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreGroup0 R) :
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
  Fixpoint reassemble_pr {X I} (R:I->reln X) (v:word X) :
    evalword (universalMarkedPreGroup R) v = setquotpr _ v.
  Proof. intros ? ? ? [|x|w|v w]. { reflexivity. } { reflexivity. }
         { simpl. assert (q := ! reassemble_pr _ _ R w). destruct q. reflexivity. }
         { simpl. assert (p := ! reassemble_pr _ _ R v). destruct p.
                  assert (q := ! reassemble_pr _ _ R w). destruct q.
                  reflexivity. } Qed.
  Lemma pr_eval_compat {X I} (R:I->reln X) (w:word X) :
    setquotpr (smallestAdequateRelation R) (evalword (wordop X) w)
    = evalword (universalMarkedPreGroup R) w.
  Proof. intros. destruct w as [|x|w|v w]. { reflexivity. } { reflexivity. }
    { exact (ap (setquotpr (smallestAdequateRelation R)) (reassemble R (word_inv w))
           @ !reassemble_pr R (word_inv w)). }
    { assert (p := !reassemble R (word_op v w)). destruct p.
      exact (!reassemble_pr R (word_op v w)). } Qed.

  (** *** abelian groups over X modulo R *)

  Definition toMarkedPreGroup {X I} (R:I->reln X) (M:gr) (el:X->M) :
      MarkedPreGroup X.
    intros. exact {| elem := M; op0 := unel _; op1 := el; op_inv := grinv _; op2 := op |}.
  Defined.
  Record MarkedGroup {X I} (R:I->reln X) :=
    make_MarkedGroup {
        m_base :> gr;
        m_mark : X -> m_base;
        m_reln : ∏ i, evalword (toMarkedPreGroup R m_base m_mark) (lhs (R i)) =
                           evalword (toMarkedPreGroup R m_base m_mark) (rhs (R i)) }.
  Arguments make_MarkedGroup {X I} R _ _ _.
  Arguments m_base {X I R} _.
  Arguments m_mark {X I R} _ x.
  Definition toMarkedPreGroup' {X I} {R:I->reln X} (M:MarkedGroup R) : MarkedPreGroup X :=
    toMarkedPreGroup R (m_base M) (m_mark M).
  Definition evalwordMM {X I} {R:I->reln X} (M:MarkedGroup R) : word X -> M :=
    evalword (toMarkedPreGroup' M).
  Definition MarkedGroup_to_hrel {X I} {R:I->reln X} (M:MarkedGroup R) : hrel (word X) :=
    λ v w , eqset (evalwordMM M v) (evalwordMM M w).
  Lemma abelian_group_adequacy {X I} (R:I->reln X) (M:MarkedGroup R) :
    AdequateRelation R (MarkedGroup_to_hrel M).
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _ _ _).
         { exact (λ i, m_reln R M i). } { reflexivity. }
         { intros ? ?. exact pathsinv0. } { intros ? ? ?. exact pathscomp0. }
         { intros ? ? ? p. simpl in p; simpl.
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros ? ? ? p. simpl in p; simpl.
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros. apply lunax. } { intros. apply runax. } { intros. apply assocax. }
         { intros ? ? p. simpl in p; simpl.
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros. apply grlinvax. } { intros. apply grrinvax. }
  Qed.
  Record MarkedGroupMap {X I} {R:I->reln X} (M N:MarkedGroup R) :=
    make_MarkedGroupMap {
        map_base :> Hom M N;
        map_mark : ∏ x, map_base (m_mark M x) = m_mark N x }.
  Arguments map_base {X I R M N} m.
  Arguments map_mark {X I R M N} m x.
  Lemma MarkedGroupMapEquality {X I} {R:I->reln X} {M N:MarkedGroup R}
        (f g:MarkedGroupMap M N) : map_base f = map_base g -> f = g.
  Proof. intros ? ? ? ? ? ? ? j.
         destruct f as [f ft], g as [g gt]; simpl in j. destruct j.
         assert(k : ft = gt). { apply funextsec; intro x. apply setproperty. } destruct k.
         reflexivity. Qed.
  Fixpoint MarkedGroupMap_compat {X I} {R:I->reln X}
           {M N:MarkedGroup R} (f:MarkedGroupMap M N) (w:word X) :
    map_base f (evalwordMM M w) = evalwordMM N w.
  Proof. intros. destruct w as [|x|w|v w].
         { exact (Monoid.unitproperty f). }
         { exact (map_mark f x). }
         { exact (monoidfuninvtoinv f (evalwordMM M w)
                @ ap (grinv N) (MarkedGroupMap_compat _ _ _ _ _ f w)). }
         { exact (Monoid.multproperty f (evalwordMM M v) (evalwordMM M w)
                  @ aptwice (λ r s, r * s)
                            (MarkedGroupMap_compat _ _ _ _ _ f v)
                            (MarkedGroupMap_compat _ _ _ _ _ f w)). } Qed.
  Lemma MarkedGroupMap_compat2 {X I} {R:I->reln X}
           {M N:MarkedGroup R} (f g:MarkedGroupMap M N) (w:word X) :
    map_base f (evalwordMM M w) = map_base g (evalwordMM M w).
  Proof. intros.
         exact (MarkedGroupMap_compat f w @ !MarkedGroupMap_compat g w). Qed.

  (** *** the universal marked abelian group over X modulo R *)

  Definition universalMarkedGroup0 {X I} (R:I->reln X) : gr.
    intros.
    { exists (univ_setwithbinop R).
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
            { exact (is_right_inverse_univ_binop R). } } } } }
  Defined.
  Definition universalMarkedGroup1 {X I} (R:I->reln X) : MarkedPreGroup X :=
    (toMarkedPreGroup R
                  (universalMarkedGroup0 R)
                  (λ x : X, setquotpr (smallestAdequateRelation R) (word_gen x))).
  Lemma universalMarkedGroup2 {X I} (R:I->reln X) (w:word X) :
    setquotpr (smallestAdequateRelation R) w = evalword (universalMarkedGroup1 R) w.
  Proof. intros.
    exact (! (ap (setquotpr (smallestAdequateRelation R)) (reassemble R w))
           @ pr_eval_compat R w). Qed.
  Definition universalMarkedGroup3 {X I} (R:I->reln X) (i:I) :
    evalword (universalMarkedGroup1 R) (lhs (R i)) =
    evalword (universalMarkedGroup1 R) (rhs (R i)).
  Proof. intros.
         exact (! universalMarkedGroup2 R (lhs (R i))
                @ iscompsetquotpr (smallestAdequateRelation R) _ _ (λ r ra, base ra i)
                @ universalMarkedGroup2 R (rhs (R i))). Qed.
  Definition universalMarkedGroup {X I} (R:I->reln X) : MarkedGroup R :=
    make_MarkedGroup R (universalMarkedGroup0 R)
                (λ x, setquotpr (smallestAdequateRelation R) (word_gen x))
                (universalMarkedGroup3 R).
  Fixpoint agreement_on_gens0 {X I} {R:I->reln X} {M:gr}
        (f g:Hom (universalMarkedGroup R) M)
        (p:∏ i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) =
                   g (setquotpr (smallestAdequateRelation R) (word_gen i)))
        (w:word X) :
          pr1 f (setquotpr (smallestAdequateRelation R) w) =
          pr1 g (setquotpr (smallestAdequateRelation R) w).
  Proof. intros. destruct w as [|x|w|v w].
         { intermediate_path (unel M). exact (Monoid.unitproperty f). exact (!Monoid.unitproperty g). }
         { apply p. }
         (* compare duplication with the proof of MarkedGroupMap_compat *)
         { simple refine (monoidfuninvtoinv f (setquotpr (smallestAdequateRelation R) w)
             @ _ @ ! monoidfuninvtoinv g (setquotpr (smallestAdequateRelation R) w)).
           apply (ap (grinv M)). apply agreement_on_gens0. assumption. }
         { simple refine (
               Monoid.multproperty f (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)
             @ _ @ !
               Monoid.multproperty g (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)).
           apply (aptwice (λ r s, r * s)).
           { apply agreement_on_gens0. assumption. }
           { apply agreement_on_gens0. assumption. } } Qed.
  Lemma agreement_on_gens {X I} {R:I->reln X} {M:gr}
        (f g:Hom (universalMarkedGroup R) M) :
        (∏ i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) =
                   g (setquotpr (smallestAdequateRelation R) (word_gen i)))
          -> f = g.
    intros ? ? ? ? ? ? p. apply Monoid.funEquality.
    apply funextsec; intro t; simpl in t.
    apply (surjectionisepitosets _ _ _ (issurjsetquotpr _)).
    { apply setproperty. } { apply agreement_on_gens0. assumption. } Qed.
  Definition universality0 {X I} {R:I->reln X} (M:MarkedGroup R) :
    universalMarkedGroup0 R -> M.
  Proof. intros ? ? ? ?.
    apply (setquotuniv _ _ (evalwordMM M)).
    exact (λ _ _ r, r (MarkedGroup_to_hrel M) (abelian_group_adequacy R M)).
  Defined.
  Definition universality1 {X I} (R:I->reln X)
                           (M:MarkedGroup R) (v w:universalMarkedGroup0 R) :
    universality0 M (v * w) = universality0 M v * universality0 M w.
  Proof. intros. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [v' j]; destruct j.
    apply (squash_to_prop (lift R w) ig); intros [w' []].
    reflexivity. Qed.
  Definition universality2 {X I} {R:I->reln X} (M:MarkedGroup R) :
    monoidfun (universalMarkedGroup R) M.
  Proof. intros. exists (universality0 M).
      split. { intros v w. apply universality1. } { reflexivity. } Defined.

  (** * universality of the universal marked abelian group *)

  Local Arguments pr1monoidfun {X Y} f x.
  Theorem iscontrMarkedGroupMap {X I} {R:I->reln X} (M:MarkedGroup R) :
        iscontr (MarkedGroupMap (universalMarkedGroup R) M).
  Proof. intros.
    assert (g := make_MarkedGroupMap X I R
                           (universalMarkedGroup R) M
                           (universality2 M) (λ x, idpath _)).
    exists g. intros f. apply MarkedGroupMapEquality.
    apply Monoid.funEquality. apply funextsec; intro v.
    isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [w []].
    exact ((ap f (universalMarkedGroup2 R w))
         @ MarkedGroupMap_compat2 f g w @ !(ap g (universalMarkedGroup2 R w))).
  Defined.
End Presentation.
Module Product.
  Definition make {I} (X:I->gr) : gr.
    intros. set (Y := Monoid.Product.make X). exists (pr1monoid Y). exists (pr2 Y).
    exists (λ y i, grinv (X i) (y i)). split.
    - intro y. apply funextsec; intro i. apply grlinvax.
    - intro y. apply funextsec; intro i. apply grrinvax. Defined.
  Definition Proj {I} (X:I->gr) (i:I) : Hom (make X) (X i).
    intros. exact (Monoid.Product.Proj X i). Defined.
  Definition Fun {I} (X:I->gr) (T:gr) (g: ∏ i, Hom T (X i)) : Hom T (make X).
    intros. exact (Monoid.Product.Fun X T g). Defined.
  Definition Eqn {I} (X:I->gr) (T:gr) (g: ∏ i, Hom T (X i))
             : ∏ i, Proj X i ∘ Fun X T g = g i.
    intros. apply Monoid.funEquality. reflexivity. Qed.
End Product.
Module Free.
  Import Presentation.
  Definition make (X:Type) := @universalMarkedGroup X empty fromempty.
End Free.
Definition ZZ := Free.make unit.
Require Import UniMath.NumberSystems.Integers.
Definition hZZ := hzaddabgr:gr. (* isomorphic to ZZ *)
