(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1b
               Foundations.hlevel2.finitesets
	       RezkCompletion.auxiliary_lemmas_HoTT
               Ktheory.Utilities.
Import RezkCompletion.pathnotations.PathNotations Utilities.Notation.
Require Ktheory.QuotientSet Ktheory.Monoid.
Close Scope multmonoid_scope.
Open Scope addmonoid_scope.
Local Notation Hom := monoidfun.
Definition incl n : stn n -> stn (S n).
  (* use dni instead *)
  intros n [i l]. exists i.
  apply (natlthlehtrans i n (S n)). { assumption. } { exact (natlehnsn n). }
Defined.
Definition finiteOperation0 (X:abmonoid) n (x:stn n->X) : X.
Proof. (* return (...((x0*x1)*x2)*...)  *)
  intros. induction n as [|n x'].
  { exact (unel _). } { exact ((x' (funcomp (incl n) x)) + x (lastelement n)). } Defined.
Goal forall (X:abmonoid) n (x:stn (S n)->X),
     finiteOperation0 X (S n) x 
  == finiteOperation0 X n (funcomp (incl n) x) + x (lastelement n).
Proof. reflexivity. Qed.
Lemma same_n {I m n} (f:nelstruct m I) (g:nelstruct n I) : m == n.
Proof. intros. apply weqtoeqstn. exact (weqcomp f (invweq g)). Qed.
Lemma fun_assoc {W X Y Z} (f:W->X) (g:X->Y) (h:Y->Z) :
  funcomp (funcomp f g) h == funcomp f (funcomp g h).
Proof. reflexivity. Defined.
Lemma uniqueness0 (X:abmonoid) n : forall I (f g:nelstruct n I) (x:I->X),
     finiteOperation0 X n (funcomp (pr1 f) x) 
  == finiteOperation0 X n (funcomp (pr1 g) x).
Proof. intros ? ?. induction n as [|n IH].
       { reflexivity. }
       { intros. simpl.
         assert (dec : decidable ( pr1 f (lastelement n) == pr1 g (lastelement n) )).
         { apply (isdeceqweqf f). apply isdeceqstn. }
         destruct dec as [e|b].
         { apply (aptwice (fun x y => x + y)).
           { rewrite <- 2 ! fun_assoc. 
             assert (f' := nelstructoncompl (pr1 f (lastelement n)) f).
             assert (g' := nelstructoncompl (pr1 g (lastelement n)) g).
             destruct e.
             (* try using weqcutonweq, dni, dnitocompl, weqdnicompl, weqdnicoprod, ... *)
             admit. }
           { exact (ap x e). } }
         { admit. } } Qed.
Definition finiteOperation1 (X:abmonoid) I : finstruct I -> (I->X) -> X.
  intros ? ? [n f] x.
  apply (finiteOperation0 X n).
  intros i. exact (x (pr1 f i)).
Defined.
Definition finiteOperation {I} (is:isfinite I) (X:abmonoid) (x:I->X) : X.
  intros. generalize is; clear is.
  refine (squash_to_set _ _ _). 
  { apply setproperty. }
  { intros fs. apply (finiteOperation1 X I fs x). }
  { intros [m f] [n g]. assert (e := same_n f g). destruct e. apply uniqueness0. }
Defined.

(** * abelian monoids by generators and relations *)
Module Presentation.
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
  Record MarkedPreAbelianMonoid X := 
    make_preAbelianMonoid {
        elem :> Type;
        op0 : elem;
        op1 : X -> elem;
        op2 : elem -> elem -> elem }.
  Arguments elem {X} M : rename.
  Arguments op0 {X M} : rename.
  Arguments op1 {X M} x : rename.
  Arguments op2 {X M} v w : rename.
  Definition wordop X := make_preAbelianMonoid X (word X) word_unit word_gen word_op.
  Fixpoint evalword {X} (Y:MarkedPreAbelianMonoid X) (w:word X) : elem Y.
    intros ? Y [|x|v w]. { exact op0. } { exact (op1 x). }
    { exact (op2 (evalword X Y v) (evalword X Y w)). } Defined.
  Definition MarkedPreAbelianMonoid_to_hrel {X} 
             (M:MarkedPreAbelianMonoid X) (is:isaset (elem M)) : 
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
        assoc : forall u v w, r (word_op (word_op u v) w) (word_op u (word_op v w));
        comm : forall v w, r (word_op v w) (word_op w v)
      }.
  Arguments make_AdequateRelation {X I} R r _ _ _ _ _ _ _ _ _ _.
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
    exists (forall r: hrel (word X), AdequateRelation R r -> r v w).
    abstract (apply impred; intro r; apply impred; intros _; apply propproperty).
  Defined.
  Lemma adequacy {X I} (R:I->reln X) : 
    AdequateRelation R (smallestAdequateRelation0 R).
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _).
         { intros ? r ra. apply base. exact ra. }
         { intros ? r ra. apply (reflex R). exact ra. }
         { intros ? ? p r ra. apply (symm R). exact ra. exact (p r ra). }
         { exact (fun u v w p q r ra => trans R r ra u v w (p r ra) (q r ra)). }
         { intros ? ? ? p r ra. apply (left_compat R). exact ra. exact (p r ra). }
         { intros ? ? ? p r ra. apply (right_compat R). exact ra. exact (p r ra). }
         { intros ? r ra. apply (left_unit R). exact ra. }
         { intros ? r ra. apply (right_unit R). exact ra. }
         { exact (fun u v w r ra => assoc R r ra u v w). } 
         { exact (fun v w r ra => comm R r ra v w). }
  Qed.
  Definition smallestAdequateRelation {X I} (R:I->reln X) : eqrel (word X).
    intros. exact (adequacy_to_eqrel R _ (adequacy R)). Defined.

  (** *** the underlying set of the abelian group with generators X and relations R *)

  Definition universalMarkedPreAbelianMonoid0 {X I} (R:I->reln X) : hSet := 
    setquotinset (smallestAdequateRelation R).
  Lemma op2_compatibility {X I} (R:I->reln X) : 
    QuotientSet.iscomprelrelfun2
      (smallestAdequateRelation R) (smallestAdequateRelation R) (smallestAdequateRelation R)
      word_op.    
  Proof. intros. split.
    { intros x x' y p r ra. exact (right_compat R r ra x x' y (p r ra)). }
    { intros x y y' p r ra. exact ( left_compat R r ra x y y' (p r ra)). } Qed.

  (** *** the multiplication on on it *)

  Definition univ_binop {X I} (R:I->reln X) : binop (universalMarkedPreAbelianMonoid0 R).
    intros. refine (QuotientSet.setquotfun2 word_op _). apply op2_compatibility. Defined.
  Definition univ_setwithbinop {X I} (R:I->reln X) : setwithbinop
             := setwithbinoppair (universalMarkedPreAbelianMonoid0 R) (univ_binop R).

  (** *** the universal pre-Abelian group *)

  Definition universalMarkedPreAbelianMonoid {X I} (R:I->reln X) : MarkedPreAbelianMonoid X.
    intros. refine (make_preAbelianMonoid X (universalMarkedPreAbelianMonoid0 R) _ _ _).
    { exact (setquotpr _ word_unit). }
    { exact (fun x => setquotpr _ (word_gen x)). }
    { exact (univ_binop _). } Defined.

  (** *** identities for the universal preabelian group *)

  Lemma lift {X I} (R:I->reln X) : issurjective (setquotpr (smallestAdequateRelation R)).
  Proof. intros. exact (issurjsetquotpr (smallestAdequateRelation R)). Qed.
  Lemma is_left_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreAbelianMonoid0 R) :
    ((univ_binop _) (setquotpr _ word_unit) w) == w.
  Proof. intros ? ? ? w'. isaprop_goal ig. { apply setproperty. } 
    apply (squash_to_prop (lift R w') ig); intros [w []].
    exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                           (fun r ra => left_unit R r ra w)). Qed.
  Lemma is_right_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreAbelianMonoid0 R) :
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
  Lemma iscomm_univ_binop {X I} (R:I->reln X) : iscomm(univ_binop R).
  Proof. intros. set (e := smallestAdequateRelation R). intros v' w'. 
         isaprop_goal ig. { apply setproperty. }
         apply (squash_to_prop (lift R v') ig); intros [v j]; destruct j.
         apply (squash_to_prop (lift R w') ig); intros [w []].
         exact (iscompsetquotpr e _ _ (fun r ra => comm R r ra v w)). Qed.
  Fixpoint reassemble_pr {X I} (R:I->reln X) (v:word X) : 
    evalword (universalMarkedPreAbelianMonoid R) v == setquotpr _ v.
  Proof. intros ? ? ? [|x|v w]. { reflexivity. } { reflexivity. }
         { simpl. assert (p := ! reassemble_pr _ _ R v). destruct p.
                  assert (q := ! reassemble_pr _ _ R w). destruct q.
                  reflexivity. } Qed.
  Lemma pr_eval_compat {X I} (R:I->reln X) (w:word X) :
    setquotpr (smallestAdequateRelation R) (evalword (wordop X) w) 
    == evalword (universalMarkedPreAbelianMonoid R) w.
  Proof. intros. destruct w as [|x|v w]. { reflexivity. } { reflexivity. } 
    { assert (p := !reassemble R (word_op v w)). destruct p. 
      exact (!reassemble_pr R (word_op v w)). } Qed.

  (** *** abelian groups over X modulo R *)

  Definition toMarkedPreAbelianMonoid {X I} (R:I->reln X) (M:abmonoid) (el:X->M) : 
      MarkedPreAbelianMonoid X.
    intros. exact {| elem := M; op0 := unel _; op1 := el; op2 := op |}.
  Defined.
  Record MarkedAbelianMonoid {X I} (R:I->reln X) := 
    make_MarkedAbelianMonoid {
        m_base :> abmonoid;
        m_mark : X -> m_base;
        m_reln : forall i, evalword (toMarkedPreAbelianMonoid R m_base m_mark) (lhs (R i)) ==
                           evalword (toMarkedPreAbelianMonoid R m_base m_mark) (rhs (R i)) }.
  Arguments make_MarkedAbelianMonoid {X I} R _ _ _.
  Arguments m_base {X I R} _.
  Arguments m_mark {X I R} _ x.
  Arguments m_reln {X I R} _ i.
  Definition relations {X I} {R:I->reln X} (M:MarkedAbelianMonoid R) := R.
  Definition toMarkedPreAbelianMonoid' {X I} {R:I->reln X} (M:MarkedAbelianMonoid R) : MarkedPreAbelianMonoid X :=
    toMarkedPreAbelianMonoid R (m_base M) (m_mark M).
  Definition evalwordMM {X I} {R:I->reln X} (M:MarkedAbelianMonoid R) : word X -> M :=
    evalword (toMarkedPreAbelianMonoid' M).
  Definition MarkedAbelianMonoid_to_hrel {X I} {R:I->reln X} (M:MarkedAbelianMonoid R) : hrel (word X) :=
    fun v w  => eqset (evalwordMM M v) (evalwordMM M w).
  Lemma abelian_group_adequacy {X I} (R:I->reln X) (M:MarkedAbelianMonoid R) :
    AdequateRelation R (MarkedAbelianMonoid_to_hrel M).
  Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _).
         { exact (fun i => m_reln M i). } { reflexivity. }
         { intros ? ?. exact pathsinv0. } { intros ? ? ?. exact pathscomp0. }
         { intros ? ? ? p. simpl in p; simpl. 
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros ? ? ? p. simpl in p; simpl. 
           unfold evalwordMM,evalword in *. destruct p. reflexivity. }
         { intros. apply lunax. } { intros. apply runax. } { intros. apply assocax. } 
         { intros. apply commax. }
  Qed.
  Record MarkedAbelianMonoidMap {X I} {R:I->reln X} (M N:MarkedAbelianMonoid R) :=
    make_MarkedAbelianMonoidMap {
        map_base :> Hom M N;
        map_mark : forall x, map_base (m_mark M x) == m_mark N x }.
  Arguments map_base {X I R M N} m.
  Arguments map_mark {X I R M N} m x.
  Lemma MarkedAbelianMonoidMapEquality {X I} {R:I->reln X} {M N:MarkedAbelianMonoid R}
        (f g:MarkedAbelianMonoidMap M N) : map_base f == map_base g -> f == g.
  Proof. intros ? ? ? ? ? ? ? j.
         destruct f as [f ft], g as [g gt]; simpl in j. destruct j.
         assert(k : ft == gt). { apply funextsec; intro x. apply setproperty. } destruct k. 
         reflexivity. Qed.
  Fixpoint MarkedAbelianMonoidMap_compat {X I} {R:I->reln X}
           {M N:MarkedAbelianMonoid R} (f:MarkedAbelianMonoidMap M N) (w:word X) :
    map_base f (evalwordMM M w) == evalwordMM N w.
  Proof. intros. destruct w as [|x|v w].
         { exact (Monoid.unitproperty f). }
         { exact (map_mark f x). }
         { exact (Monoid.multproperty f (evalwordMM M v) (evalwordMM M w)
                  @ aptwice (fun r s => r + s) 
                            (MarkedAbelianMonoidMap_compat _ _ _ _ _ f v) 
                            (MarkedAbelianMonoidMap_compat _ _ _ _ _ f w)). } Qed.
  Lemma MarkedAbelianMonoidMap_compat2 {X I} {R:I->reln X} 
           {M N:MarkedAbelianMonoid R} (f g:MarkedAbelianMonoidMap M N) (w:word X) :
    map_base f (evalwordMM M w) == map_base g (evalwordMM M w).
  Proof. intros. 
         exact (MarkedAbelianMonoidMap_compat f w @ !MarkedAbelianMonoidMap_compat g w). Qed.

  (** *** the universal marked abelian group over X modulo R *)

  Definition universalMarkedAbelianMonoid0 {X I} (R:I->reln X) : abmonoid.
    intros. 
    { exists (univ_setwithbinop R). split.
      { exists (isassoc_univ_binop R). 
        exists (setquotpr _ word_unit). 
        split. 
            { exact (is_left_unit_univ_binop R). }
            { exact (is_right_unit_univ_binop R). } }
      exact (iscomm_univ_binop R). } Defined.
  Definition universalMarkedAbelianMonoid1 {X I} (R:I->reln X) : MarkedPreAbelianMonoid X :=
    (toMarkedPreAbelianMonoid R 
                  (universalMarkedAbelianMonoid0 R)
                  (fun x : X => setquotpr (smallestAdequateRelation R) (word_gen x))). 
  Lemma universalMarkedAbelianMonoid2 {X I} (R:I->reln X) (w:word X) : 
    setquotpr (smallestAdequateRelation R) w == evalword (universalMarkedAbelianMonoid1 R) w.
  Proof. intros.
    exact (! (ap (setquotpr (smallestAdequateRelation R)) (reassemble R w))
           @ pr_eval_compat R w). Qed.
  Definition universalMarkedAbelianMonoid3 {X I} (R:I->reln X) (i:I) : 
    evalword (universalMarkedAbelianMonoid1 R) (lhs (R i)) ==
    evalword (universalMarkedAbelianMonoid1 R) (rhs (R i)).
  Proof. intros.
         exact (! universalMarkedAbelianMonoid2 R (lhs (R i))
                @ iscompsetquotpr (smallestAdequateRelation R) _ _ (fun r ra => base ra i)
                @ universalMarkedAbelianMonoid2 R (rhs (R i))). Qed.
  Definition universalMarkedAbelianMonoid {X I} (R:I->reln X) : MarkedAbelianMonoid R :=
    make_MarkedAbelianMonoid R (universalMarkedAbelianMonoid0 R) 
                (fun x => setquotpr (smallestAdequateRelation R) (word_gen x)) 
                (universalMarkedAbelianMonoid3 R).
  Fixpoint agreement_on_gens0 {X I} {R:I->reln X} {M:abmonoid}
        (f g:Hom (universalMarkedAbelianMonoid R) M)
        (p:forall i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) ==
                   g (setquotpr (smallestAdequateRelation R) (word_gen i)))
        (w:word X) :
          pr1 f (setquotpr (smallestAdequateRelation R) w) ==
          pr1 g (setquotpr (smallestAdequateRelation R) w).
  Proof. intros. destruct w as [|x|v w].
         { intermediate_path (unel M). exact (Monoid.unitproperty f). exact (!Monoid.unitproperty g). }
         { apply p. }
         (* compare duplication with the proof of MarkedAbelianMonoidMap_compat *)
         { refine (
               Monoid.multproperty f (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)
             @ _ @ !
               Monoid.multproperty g (setquotpr (smallestAdequateRelation R) v)
                   (setquotpr (smallestAdequateRelation R) w)).
           apply (aptwice (fun r s => r + s)).
           { apply agreement_on_gens0. assumption. }
           { apply agreement_on_gens0. assumption. } } Qed.
  Lemma agreement_on_gens {X I} {R:I->reln X} {M:abmonoid}
        (f g:Hom (universalMarkedAbelianMonoid R) M) :
        (forall i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) ==
                   g (setquotpr (smallestAdequateRelation R) (word_gen i))) 
          -> f == g.
    intros ? ? ? ? ? ? p. apply Monoid.funEquality.
    apply funextsec; intro t; simpl in t. 
    apply (surjectionisepitosets _ _ _ (issurjsetquotpr _)).
    { apply setproperty. } { apply agreement_on_gens0. assumption. } Qed.
  Definition universality0 {X I} {R:I->reln X} (M:MarkedAbelianMonoid R) : 
    universalMarkedAbelianMonoid0 R -> M.
  Proof. intros ? ? ? ?. 
    apply (setquotuniv _ _ (evalwordMM M)).
    exact (fun _ _ r => r (MarkedAbelianMonoid_to_hrel M) (abelian_group_adequacy R M)).
  Defined.
  Definition universality1 {X I} (R:I->reln X) 
                           (M:MarkedAbelianMonoid R) (v w:universalMarkedAbelianMonoid0 R) :
    universality0 M (v + w) == universality0 M v + universality0 M w.
  Proof. intros. isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [v' j]; destruct j.
    apply (squash_to_prop (lift R w) ig); intros [w' []].
    reflexivity. Qed.
  Definition universality2 {X I} {R:I->reln X} (M:MarkedAbelianMonoid R) : 
    monoidfun (universalMarkedAbelianMonoid R) M.
  Proof. intros. exists (universality0 M).
      split. { intros v w. apply universality1. } { reflexivity. } Defined.

  (** * universality of the universal marked abelian group *)

  Local Arguments pr1monoidfun {X Y} f x.
  Theorem iscontrMarkedAbelianMonoidMap {X I} {R:I->reln X} (M:MarkedAbelianMonoid R) :
        iscontr (MarkedAbelianMonoidMap (universalMarkedAbelianMonoid R) M).
  Proof. intros. 
    assert (g := make_MarkedAbelianMonoidMap X I R 
                           (universalMarkedAbelianMonoid R) M 
                           (universality2 M) (fun x => idpath _)).
    exists g. intros f. apply MarkedAbelianMonoidMapEquality.
    apply Monoid.funEquality. apply funextsec; intro v.
    isaprop_goal ig. { apply setproperty. }
    apply (squash_to_prop (lift R v) ig); intros [w []].
    exact ((ap f (universalMarkedAbelianMonoid2 R w)) 
         @ MarkedAbelianMonoidMap_compat2 f g w @ !(ap g (universalMarkedAbelianMonoid2 R w))).
  Defined.
End Presentation.
Module Free.
  Import Presentation.
  Definition make (X:Type) := @universalMarkedAbelianMonoid X empty fromempty.
End Free.
Definition NN := Free.make unit.

Module NN_agreement.
  Import Presentation.
  Definition mult {X:abmonoid} (n:nat) (x:X) : X.
    intros. induction n. exact (unel _). exact (x + IHn). Defined.
  Local Notation "n * x" := ( mult n x ). 
  Lemma mult_one (n:nat) : n * (1 : nataddabmonoid) == n.
  Proof. intro. induction n. { reflexivity. } { exact (ap S IHn). } Qed.
  Lemma mult_fun {X Y:abmonoid} (f:Hom X Y) (n:nat) (x:X) : f(n*x) == n*f x.
  Proof. intros. induction n. { exact (Monoid.unitproperty f). }
         { refine (Monoid.multproperty f x (n*x) @ _).
           { simpl. simpl in IHn. destruct IHn. reflexivity. } } Qed.
  Lemma uniq_fun {X:abmonoid} (f g:Hom nataddabmonoid X) :
    f 1 == g 1 -> homot f g.
  Proof. intros ? ? ? e n.
         induction n.
         { exact (Monoid.unitproperty f @ !Monoid.unitproperty g). }
         { exact (Monoid.multproperty f 1 n 
                @ aptwice (fun x y => x+y) e IHn 
                @ !Monoid.multproperty g 1 n). } Qed.
  Definition weq_NN_nataddabmonoid : weq NN nataddabmonoid.
  Proof.
    set (R := Presentation.relations NN).
    set (one := Presentation.m_mark NN tt).
    set (markednat := 
           make_MarkedAbelianMonoid R nataddabmonoid (fun _ => 1) fromemptysec).
    exists (map_base (the (iscontrMarkedAbelianMonoidMap markednat))).
    refine (gradth _ _ _ _).
    { intros m. { exact (m * one). } }
    { intros w.
      apply (squash_to_prop (lift R w)).
      { apply setproperty. }
      { intros [v v'].
        rewrite <- v'.
        clear v' w.
        Close Scope multmonoid_scope.
        Open Scope addmonoid_scope.
        Close Scope multmonoid.
        Open Scope addmonoid.
        induction v.
        { admit. }
        { admit. }
        { admit. } } }
    { intros m.
      admit.
      }
    Defined.
End NN_agreement.
