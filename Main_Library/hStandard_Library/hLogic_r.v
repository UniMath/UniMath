(************************************************************************)
(* This is the modification of the original Logic.v file from the Coq standard library. *)
(* We remove all the uses of Prop and replaced them by hProp. *)
(************************************************************************)


Set Implicit Arguments.


Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Require Export Notations hProp_r hSet_r.

(** * Propositional connectives *)

(** [True] is the always true proposition *)
Notation True := ( htrue ) .


(** [False] is the always false proposition *)
Notation False := ( hfalse ) .

(** [not A], written [~A], is the negation of [A] *)
Definition not ( A : hProp ) : hProp := hProppair ( A -> False ) ( isapropneg A ) .
Canonical Structure not . 

Notation "~ x" := (not x) : type_scope.

Hint Unfold not: core.

  (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj p q] is a proof of [A /\ B] as soon as
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

Notation and := hconj .

Notation "A /\ B" := (and A B) : type_scope.

Section Conjunction.

  Variables A B : hProp.

  Theorem proj1 : A /\ B -> A.
  Proof.
    destruct 1; trivial.
  Defined. 

  Theorem proj2 : A /\ B -> B.
  Proof.
    destruct 1; trivial.
  Defined. 

End Conjunction.

(** [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

Notation or := hdisj .

Notation "A \/ B" := (or A B) : type_scope.

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Print Canonical Projections.

Definition iff (A B: hProp) :=  ( himpl A  B ) /\ ( himpl B A ) .

Notation "A <-> B" := (iff A B) : type_scope.

Section Equivalence.

Theorem iff_refl : forall A : hProp, A <-> A.
  Proof.
    split.  destruct A as [ T is ].  simpl. apply (fun t : T  => t).  destruct A as [ T is ].  simpl. apply (fun t : T  => t). 
  Defined. 

Theorem iff_trans : forall A B C: hProp, (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    intros A B C [H1 H2] [H3 H4]. split. destruct A as [ T1 is1]. destruct B as [T2 is2] . destruct C as  [T3 is3].  simpl. simpl in  H1. simpl in H2 . simpl in  H3 . simpl in  H4 .     auto.
destruct A as [ T1 is1]. destruct B as [T2 is2] . destruct C as  [T3 is3].  simpl. simpl in  H1. simpl in H2 . simpl in  H3 . simpl in  H4 .     auto.
  Defined. 

Theorem iff_sym : forall A B: hProp, (A <-> B) -> (B <-> A).
  Proof.
    intros A B [H1 H2]; split.
destruct A as [ T1 is1 ] . destruct B as [ T2 is2 ]. simpl in H1. simpl in H2. auto. 
destruct A as [ T1 is1 ] . destruct B as [ T2 is2 ]. simpl in H1. simpl in H2. auto.     
  Defined. 

End Equivalence.

Hint Unfold iff: extcore.

(** Some equivalences *)

Theorem neg_false : forall A : hProp, ~ A <-> (A <-> False).
Proof.
intro A; unfold not; split.
intro H; split; [exact H | intro H1; elim H1].
intros [H _]; exact H.
Defined. 

Theorem and_cancel_l : forall A B C : hProp,
  (B -> A) -> (C -> A) -> ((A /\ B <-> A /\ C) <-> (B <-> C)).
Proof.
intros A B C fba fca. 

destruct A as [ T1 is1 ] . destruct B as [ T2 is2 ]. destruct C as [ T3 is3 ] .  simpl in fba.  simpl in fca. simpl. split. 

intro a1.  destruct a1 as [ a2 a3 ] . split.  
intro t2.  apply ( pr22 _ _ ( a2 ( dirprodpair _ _ (fba t2) t2 ))). 
intro t3.  apply ( pr22 _ _ ( a3 ( dirprodpair _ _ (fca t3) t3 ))).

intro a1. destruct a1 as [ a2 a3 ] . split.  
intro t2.  destruct t2 as [ t1 t3 ]. apply (dirprodpair _ _ t1 (a2 t3)). 
intro t2. destruct t2 as [ t1 t3 ] . apply (dirprodpair _ _ t1 ( a3 t3)).
Defined.
 

Theorem and_cancel_r : forall A B C : hProp,
  (B -> A) -> (C -> A) -> ((B /\ A <-> C /\ A) <-> (B <-> C)).
Proof.
intros A B C fba fca. 

destruct A as [ T1 is1 ] . destruct B as [ T2 is2 ]. destruct C as [ T3 is3 ] .  simpl in fba.  simpl in fca. simpl. split. 

intro a1.  destruct a1 as [ a2 a3 ] . split.  
intro t2.  apply ( pr21 _ _ ( a2 ( dirprodpair _ _ t2 (fba t2) ))). 
intro t3.  apply ( pr21 _ _ ( a3 ( dirprodpair _ _ t3 (fca t3) ))).

intro a1. destruct a1 as [ a2 a3 ] . split.  
intro t3.  destruct t3 as [ t2 t1 ]. apply (dirprodpair _ _ (a2 t2) t1 ). 
intro t2. destruct t2 as [ t3 t1 ] . apply (dirprodpair _ _ ( a3 t3) t1 ).
Defined.


Theorem and_comm : forall A B : hProp, A /\ B <-> B /\ A.
Proof. intros A B. destruct A as [ A isa ] . destruct B as [ B isb ]. split.

simpl. intro ab. destruct ab as [ a b ] . apply (dirprodpair _ _ b a).
simpl. intro ba. destruct ba as [ b a ] . apply (dirprodpair _ _ a b).
  
Defined. 



Theorem and_assoc : forall A B C : hProp, (A /\ B) /\ C <-> A /\ B /\ C.
Proof. intros A B C. destruct A as [ A isa ] . destruct B as [ B isb ]. destruct C as [ C isc ]. split.

simpl.  intro abc.  destruct abc as [ ab c ].  destruct ab as [ a b ]. apply ( dirprodpair _ _  a ( dirprodpair _ _ b c ) ) .
simpl.  intro abc.  destruct abc as [ a bc ].  destruct bc as [ b c ]. apply ( dirprodpair _ _  ( dirprodpair _ _ a b ) c ) .

Defined. 


Lemma nor_l : forall A B : hProp , ~ A -> ( A \/ B -> B ).
Proof. intros A B na ab.  apply hinhuniv with ( coprod A B ). intro acb. destruct acb.  apply (initmap _ (na h)). assumption.  assumption.  Defined. 

Lemma nor_r : forall A B : hProp , ~ A -> ( B \/ A -> B ).
Proof. intros A B na ba.  apply hinhuniv with ( coprod B A ). intro bca. destruct bca.  assumption.  apply (initmap _ (na h)). assumption.   Defined.


Theorem or_cancel_l : forall A B C : hProp,
  (B -> ~ A) -> (C -> ~ A) -> ((A \/ B <-> A \/ C) <-> (B <-> C)).
Proof.  intros A B C bna cna.  split.

intro isis. split. intro b. destruct isis as [ abac acab ] .   set ( ac := abac ( hinhpr _  ( ii2 A _ b ) ) ) .  set ( na := bna b ). apply ( nor_l na ac ) .  
 intro c. destruct isis as [ abac acab ] .   set ( ab := acab ( hinhpr _  ( ii2 A _ c ) ) ) .  set ( nc := cna c ). apply ( nor_l nc ab ) . 

intro beqc.  destruct beqc as [ btoc ctob ] . split.  
intro aorb.  simpl in btoc. apply ( hinhfunct _ _ ( coprodf _ _ _ _ ( fun a:A => a) btoc )).  assumption.  
intro aorc.  simpl in ctob. apply ( hinhfunct _ _ ( coprodf _ _ _ _ ( fun a:A => a) ctob )).  assumption.  

Defined.
 


Theorem or_cancel_r : forall A B C : hProp,
  (B -> ~ A) -> (C -> ~ A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
Proof. intros A B C bna cna. split. 

intro isis. split. intro b. destruct isis as [ baca caba ] .   set ( ca := baca ( hinhpr _  ( ii1 _ A b ) ) ) .  set ( na := bna b ). apply ( nor_r na ca ) .  
 intro c. destruct isis as [ baca caba ] .   set ( ba := caba ( hinhpr _  ( ii1 _ A c ) ) ) .  set ( nc := cna c ). apply ( nor_r nc ba ) . 

intro beqc.  destruct beqc as [ btoc ctob ] . split.  
intro bora.  simpl in btoc. apply ( hinhfunct _ _ ( coprodf _ _ _ _  btoc ( fun a:A => a) )).  assumption.  
intro cora.  simpl in ctob. apply ( hinhfunct _ _ ( coprodf _ _ _ _ ctob  ( fun a:A => a) )).  assumption.  

Defined.
 


Theorem or_comm : forall A B : hProp, (A \/ B) <-> (B \/ A).
Proof. intros A B . split. 
 intro aorb. apply ( hinhfunct _ _ ( coprodcomm A B ) aorb ) . 
 intro bora. apply ( hinhfunct _ _ ( coprodcomm B A ) bora ) .
Defined. 



Theorem or_assoc : forall A B C : hProp, (A \/ B) \/ C <-> A \/ B \/ C.
Proof.  intros A B C . split. 
 intro aorborc.  
assert (int1 :  ishinh ( coprod ( coprod A B ) C ) ).      apply ( hinhcoprod_l (coprod  A B ) C ).   assumption. 
assert (int2 : ishinh  ( coprod A (coprod B C ) ) ) . apply ( hinhfunct _ _  ( coprodasstor A B C ) ).  assumption. 
apply ( hinhfunct _ _ (coprodf A ( coprod B C ) A ( ishinh ( coprod B C ) ) ( fun a : A => a ) ( hinhpr ( coprod B C ) ) ) ).  assumption. 

intro aorborc.  
assert (int1 :  ishinh ( coprod A ( coprod B C ) ) ).      apply ( hinhcoprod_r A (coprod  B C ) ).   assumption. 
assert (int2 : ishinh  ( coprod  (coprod A B )  C ) ) . apply ( hinhfunct _ _  ( coprodasstol A B C ) ).  assumption. 
apply ( hinhfunct _ _ (coprodf  _ _ _ _  ( hinhpr ( coprod A B ) ) ( fun c : C => c ) ) ).  assumption. 

Defined. 



Theorem and_iff_compat_l : forall A B C : hProp,
  (B <-> C) -> (A /\ B <-> A /\ C).
Proof.  intros A B C beqc . split. 

intro ab.  destruct beqc as [ btoc ctob ].  simpl.  destruct ab as [ a b ].  apply ( dirprodpair _ _ a ( btoc b ) ). 
intro ac. destruct beqc as [ btoc ctob ]. simpl. destruct ac as [ a c ]. apply ( dirprodpair _ _ a ( ctob c ) ) .

Defined.




Theorem and_iff_compat_r : forall A B C : hProp,
  (B <-> C) -> (B /\ A <-> C /\ A).
Proof.  intros A B C beqc . split. 

intro ba.  destruct beqc as [ btoc ctob ].  simpl.  destruct ba as [ b a ].  apply ( dirprodpair _ _ ( btoc b ) a ). 
intro ca. destruct beqc as [ btoc ctob ]. simpl. destruct ca as [ c a ]. apply ( dirprodpair _ _ ( ctob c ) a ) .

Defined.



Theorem or_iff_compat_l : forall A B C : hProp,
  (B <-> C) -> (A \/ B <-> A \/ C).
Proof.  intros A B C beqc . destruct beqc as [ btoc ctob ]. split. 

intro aorb.  apply (hinhfunct _ _ ( coprodf _ _ _ _ ( fun a : A => a ) btoc )). assumption.    
intro cora .  apply (hinhfunct _ _ ( coprodf _ _ _ _ ( fun a : A => a ) ctob )). assumption.   

Defined.








Theorem or_iff_compat_r : forall A B C : hProp,
  (B <-> C) -> (B \/ A <-> C \/ A).
Proof. intros A B C beqc . destruct beqc as [ btoc ctob ]. split. 

intro bora.  apply (hinhfunct _ _ ( coprodf _ _ _ _  btoc ( fun a : A => a ) )). assumption.    
intro aorc .  apply (hinhfunct _ _ ( coprodf _ _ _ _ ctob  ( fun a : A => a ) )). assumption.   

Defined.





Lemma iff_and : forall A B : hProp, (A <-> B) -> (himpl A B) /\ (himpl B A).
Proof. intros. trivial. 
Defined. 


Lemma iff_to_and : forall A B : hProp, (A <-> B) <-> (himpl A B) /\ (himpl B A).
Proof. intros. split. intro aeqb.  trivial. intro aeqb. trivial. 
Defined. 









(** [ (IF_then_else P Q R) ], written [ IF P then Q else R ] denotes
    either [ P ] and [ Q ], or [ ~P ] and [ Q ] *)

Definition IF_then_else (P Q R : hProp) := P /\ Q \/ ~ P /\ R.

Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
  (at level 200, right associativity) : type_scope.

(** * First-order quantifiers *)

(** [ ex P ], or simply [ exists x, P x ], or also [ exists x:A, P x ],
    expresses the existence of an [ x ] of some type [ A ] in [ Set ] which
    satisfies the predicate [ P ].  This is existential quantification.

    [ ex2 P Q ], or simply [ exists2 x, P x & Q x ], or also
    [ exists2 x:A, P x & Q x ], expresses the existence of an [ x ] of
    type [ A ] which satisfies both predicates [ P ] and [ Q ].

    Universal quantification is primitively written [ forall x:A, Q ]. By
    symmetry with existential quantification, the construction [ all P ]
    is provided too.
*)

(** Remark: [ exists x, Q ] denotes [ ex (fun x => Q) ] so that [ exists x,
   P x ] is in fact equivalent to [ ex (fun x => P x) ] which may be not
   convertible to [ ex P ] if [ P ] is not itself an abstraction *)


Definition  ex (A : UU0 ) ( P : A -> hProp ) : hProp := ishinh_hprop ( total2 A P ) . 

Definition ex2 ( A : UU0 ) ( P Q : A -> hProp ) : hProp := ishinh_hprop ( total2 A ( fun a : A => ( P a ) /\ ( Q a ) ) ) . 
 

Definition all (A:Type) (P:A -> hProp) := forall x:A, P x. 

(* Rule order is important to give printing priority to fully typed exists *)

Notation "'exists' x , p" := (ex (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : t , p" := (ex (fun x:t => p))
  (at level 200, x ident, right associativity,
    format "'[' 'exists'  '/  ' x  :  t ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (ex2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

(** Derived rules for universal quantification *)

Section universal_quantification.

  Variable A : UU0.
  Variable P : A -> hProp.

  Theorem inst : forall x:A, all (fun x => P x) -> P x.
  Proof.
    unfold all in |- *; auto.
  Defined.

  Theorem gen : forall ( B : hProp) (f:forall y:A, B -> P y), B -> all P.
  Proof.
    red in |- *; auto.
  Defined.

End universal_quantification.

(** * Equality *)

(** [ eq x y ], or simply [ x=y ] expresses the equality of [ x ] and
    [ y ] with values in hProp. Both [ x ] and [ y ] must belong to the same type [ A ].
    
    The  properties (reflexivity, symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [ x ] and [ y ] can be
    made explicit using the notation [ x = y :> A ]. This is Leibniz equality
    as it expresses that [ x ] and [ y ] are equal iff every h-property on
    [ A ] which is true of [ x ] is also true of [ y ] *)

Definition eq ( A : UU0 ) ( x  y : A ) : hProp := ishinh_hprop ( paths _ x y ) .
    

Notation  "x = y :> A" := (@eq A x y) : type_scope.


Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Implicit Arguments eq [ [A ]  ].

(* Implicit Arguments eq_ind [ A ].
Implicit Arguments eq_rec [ A ].
Implicit Arguments eq_rect [ A ]. *)

Hint Resolve I conj or_introl or_intror : core.
Hint Resolve ex_intro ex_intro2: core.

Section Logic_lemmas.

  Theorem absurd : forall A C : hProp, A -> ~ A -> C.
  Proof.
    unfold not in |- *; intros A C h1 h2.
    destruct (h2 h1).
  Defined. 

  Section equality.

    Variables A B : UU0 .
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_refl : x = x .
    Proof. apply ( hinhpr _ ( idpath _ x) ) .
    Defined. 

    Theorem eq_sym : x = y -> y = x.
    Proof. intro xeqy. 
      apply ( hinhfunct _ _ ( pathsinv0 _ x y  ) ). assumption. 
    Defined.
   

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof. intros xeqy yeqz . apply (hinhand _ _ xeqy yeqz). intro d.  destruct d as [ pxy pyz ]. apply (hinhpr _ ( pathscomp0 _ _ _ _ pxy pyz ) ) .  
    Defined.
   

    Theorem f_equal : x = y -> f x = f y.
    Proof. intro xeqy . apply ( hinhfunct _ _ ( maponpaths _ _ f x y ) ). assumption. 
    Defined.
   

  End equality.

  Theorem not_eq_sym ( A : UU0 ) ( x y : A ) : x <> y -> y <> x.
    Proof.
      red in |- * . intros h1 h2 . apply h1 . apply eq_sym. assumption. 
    Defined. 


  Definition eq_ind_r :
    forall ( A : UU0 ) ( x : A ) ( P : A -> hProp), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0.  
    assert ( f : paths _ y x -> P y ). intro e. destruct e. assumption. 
    apply hinhuniv with (paths _ y x ). assumption. assumption.  
  Defined.

(** In the original logic.v the following two results use singleton elimination which is incompatible with the univalent model. However these results can still be proved using an additional assumption - that the underlying type A is an hSet. Since we do not use the syntactic [ Set ] of Coq the corresponding results become alsmost identical . *)


  Definition eq_rec_r :
    forall ( A : hSet ) ( x : A ) ( P : A -> UU0 ), P x -> forall y : A, y = x -> P y.
    intros A x P H y H0.  
    assert ( e : paths_hprop _ y x ) . apply hinhprinv . assumption.  destruct e.  assumption. 
  Defined.


  Definition  eq_rect_r :
  forall ( A : UU0 ) (is : isaset A ) ( x : A ) ( P : A -> UU0 ) , P x ->  forall y : A, y = x -> P y.
  intros A is x P H y H0.  set ( B := hSetpair A is ) .
    assert ( e : paths_hprop B y x ) . apply hinhprinv . assumption.  destruct e.  assumption. 
  Defined.
    
End Logic_lemmas.

Theorem f_equal2 :
  forall ( A1 A2 B : UU0 ) (f: A1 -> A2 -> B) (x1 y1 : A1 )
    (x2 y2 : A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof. intros A1 A2 B f x1 y1 x2 y2 e1 e2 . apply ( hinhand _ _ e1 e2 ) . 

(** At this point the proof engine makes a step which I do not understand. It seems to use something automatically which I did not tell it about. *)

intro dp. destruct dp as [ p1 p2 ].  destruct p1. destruct p2. apply  eq_refl. 
  
Defined. 

Theorem f_equal3 :
  forall (A1 A2 A3 B: UU0 ) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.  intros A1 A2 A3 B f x1 y1 x2 y2 x3 y3 e1 e2 c3. apply ( hinhand _ _ e1 e2 ) . 

(** At this point the proof engine makes a step which I do not understand. It seems to use something automatically which I did not tell it about. *)

intro dp. destruct dp as [ p1 p2 ].  destruct p1. destruct p2.  apply f_equal. assumption. 
  
Defined. 

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B : UU0 ) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.  intros A1 A2 A3 A4 B f x1 y1 x2 y2 x3 y3 x4 y4 e1 e2 e3 e4. apply ( hinhand _ _ e1 e2 ). intro dp. destruct dp as [ p1 p2 ] . destruct p1. destruct p2. apply f_equal2. assumption. assumption.   
  
Defined. 

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B : UU0 ) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.  intros A1 A2 A3 A4 A5 B f x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 e1 e2 e3 e4 e5. apply ( hinhand _ _ e1 e2 ). intro dp. destruct dp as [ p1 p2 ] . destruct p1. destruct p2. apply f_equal3. assumption. assumption. assumption.   
  
Defined.

(* Aliases *)

Notation sym_eq := eq_sym (only parsing).
Notation trans_eq := eq_trans (only parsing).
Notation sym_not_eq := not_eq_sym (only parsing).

Notation refl_equal := eq_refl (only parsing).
Notation sym_equal := eq_sym (only parsing).
Notation trans_equal := eq_trans (only parsing).
Notation sym_not_equal := not_eq_sym (only parsing).

Hint Immediate eq_refl eq_sym not_eq_sym: core.

(** Basic definitions about relations and properties *)

Definition subrelation :
 forall ( A B : UU0 ) (R R' : A -> B -> hProp) , hProp.
 intros A B R R'.  split with ( forall x y, R x y -> R' x y ) . apply impred.  intro t. apply impred. intro t0. apply impred. intro.  apply ( uu1.pr22 _ _ ( R' t t0 ) ) .
Defined. 

Definition unique :
 forall ( A : UU0 ) ( P : A -> hProp ) ( x : A ) , hProp .
  intros A P x . 
 assert ( is : isaprop ( forall ( x' : A ), P x' -> x=x') ) .   apply impred.   intro t. apply impred.  intro.  apply (uu1.pr22 _ _ ( x = t ) ) .  
 set (sc := hProppair ( forall ( x' : A ), P x' -> x=x') is ). apply  ( P x /\ sc ) .
Defined. 

Definition uniqueness : 
 forall ( A : UU0 ) ( P : A -> hProp) , hProp. 
intros A P. assert (is : isaprop ( forall x y, P x -> P y -> x = y) ). apply impred. intro. apply impred. intro. apply impred. intro. apply impred. intro. apply (uu1.pr22 _ _ ( t = t0 ) ) . apply ( hProppair _ is ) . 
Defined .

(** Unique existence *)

Notation "'exists' ! x , P" := ( ex (unique (fun x => P) ) )
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x ,  '/  ' P ']'") : type_scope.
Notation "'exists' ! x : A , P" :=
  ( ex ( unique (fun x:A => P) ) )
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x  :  A ,  '/  ' P ']'") : type_scope.


Lemma unique_existence : forall ( A : UU0 ) ( P : A -> hProp ),
  ((exists x : A , P x) /\ uniqueness P) <-> (exists! x : A , P x).
Proof.
  intros A P; split.
  intro x . destruct x as [ x is ] . simpl.  apply ( hinhand _ _ x ( hinhpr _ is ) ).  simpl. intro dp. destruct dp as [ p1 p2 ] . 
  assert ( tt : (total2 A
        (fun x0 : A =>
         dirprod (P x0) (forall x' : A, P x' -> ishinh (paths A x0 x'))))). destruct p1 as [ p1 is1 ] . split with p1 . split with is1. intro x' . intro px' . apply ( p2 p1 x' is1 px' ) .   apply hinhpr. assumption. 
  intro xx .  apply hinhuniv with (total2 A
        (fun x0 : A =>
         dirprod (P x0) (forall x' : A, P x' -> ishinh (paths A x0 x')))).  intro tt.  split.  simpl.  set ( ttt := tpair A ( fun x0 : A => P x0 ) (pr21 _ _ tt ) (pr21 _ _ (pr22 _ _ tt ) ) ) . simpl in ttt. apply (hinhpr _ ttt).  simpl. destruct tt as [ t1 t2 ] . destruct t2 as [ t2 t3 ] . intros x y . set ( e1 := t3 x ). set ( e2 := t3 y ) .
 intros px py .  set ( ee1 := (eq_sym (e1 px) )). set (ee2 := e2 py). apply (eq_trans ee1 ee2). assumption.   
Defined. 


(** * Being inhabited *)

(** The predicate [inhabited] is directly replaced by [ ishinh_hprop ] 
*)

Notation inhabited := ishinh_hprop. 
Notation inhabits := hinhpr.

(* Hint Resolve inhabits: core. *)

Lemma exists_inhabited : forall ( A : UU0 ) ( P : A -> hProp ),
  (exists x, P x) -> inhabited A.
Proof. intros A P xe.  simpl in xe. apply hinhuniv with ( total2 A P ) .   intro tt.  apply ( hinhpr _ ( pr21 _ _ tt ) ) . assumption. 
Defined. 

(** Declaration of stepl and stepr for eq and iff *)

Lemma eq_stepl : forall ( A : UU0 ) (x y z : A), x = y -> x = z -> z = y.
Proof.
intros A x y z H1 H2.  set ( H22 := eq_sym H2 ).  apply (eq_trans H22 H1 ) .  
Defined. 


Declare Left Step eq_stepl.
Declare Right Step eq_trans.

Lemma iff_stepl : forall A B C : hProp, (A <-> B) -> (A <-> C) -> (C <-> B).
Proof.
intros A B C aeqb aeqc. destruct aeqb as [ atob btoa ] . destruct aeqc as [ atoc ctoa ] . split.  simpl.   auto. simpl. auto. 
Defined.


Declare Left Step iff_stepl.
Declare Right Step iff_trans.







(* End of the file hLogic_r.v *)






(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)





