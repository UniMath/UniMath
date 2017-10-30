(* -*- coding: utf-8 *)

(** * Group actions *)

Require Import UniMath.Algebra.Monoids_and_Groups
               UniMath.Foundations.UnivalenceAxiom
               UniMath.Combinatorics.OrderedSets
               UniMath.Ktheory.Utilities.
Unset Automatic Introduction.

(** ** Definitions *)

Definition action_op G X := G -> X -> X.

Record ActionStructure (G:gr) (X:hSet) :=
  make {
      act_mult : action_op G X;
      act_unit : ∏ x, act_mult (unel _) x = x;
      act_assoc : ∏ g h x, act_mult (op g h) x = act_mult g (act_mult h x)
    }.
Arguments act_mult {G _} _ g x.

Module Pack.
  Definition ActionStructure' (G:gr) (X:hSet) :=
         ∑ act_mult : action_op G X,
         ∑ act_unit : ∏ x, act_mult (unel _) x = x,
      (* act_assoc : *) ∏ g h x, act_mult (op g h) x = act_mult g (act_mult h x).
  Definition pack {G:gr} {X:hSet} : ActionStructure' G X -> ActionStructure G X
    := λ ac, make G X (pr1 ac) (pr1 (pr2 ac)) (pr2 (pr2 ac)).
  Definition unpack {G:gr} {X:hSet} : ActionStructure G X -> ActionStructure' G X
    := λ ac, (act_mult ac,,(act_unit _ _ ac,,act_assoc _ _ ac)).
  Definition h {G:gr} {X:hSet} (ac:ActionStructure' G X) : unpack (pack ac) = ac
    := match ac as t return (unpack (pack t) = t)
       with (act_mult,,(act_unit,,act_assoc)) => idpath (act_mult,,(act_unit,,act_assoc)) end.
  Definition k {G:gr} {X:hSet} (ac:ActionStructure G X) : pack (unpack ac) = ac
    := match ac as i return (pack (unpack i) = i)
       with make _ _ act_mult act_unit act_assoc => idpath _ end.
  Lemma weq (G:gr) (X:hSet) : (ActionStructure' G X) ≃ (ActionStructure G X).
  Proof. intros. exists pack. intros ac. exists (unpack ac,,k ac). intros [ac' m].
         destruct m. assert (H := h ac'). destruct H. reflexivity. Qed.
End Pack.

Lemma isaset_ActionStructure (G:gr) (X:hSet) : isaset (ActionStructure G X).
Proof. intros. apply (isofhlevelweqf 2 (Pack.weq G X)).
       apply isofhleveltotal2.
       { apply impred; intro g. apply impred; intro x. apply setproperty. }
       intro op. apply isofhleveltotal2.
       { apply impred; intro x. apply hlevelntosn. apply setproperty. }
       intro un. apply impred; intro g. apply impred; intro h. apply impred; intro x.
       apply hlevelntosn. apply setproperty. Qed.

Definition Action (G:gr) := total2 (ActionStructure G).
Definition makeAction {G:gr} (X:hSet) (ac:ActionStructure G X) :=
  X,,ac : Action G.

Definition ac_set {G:gr} (X:Action G) := pr1 X.
Coercion ac_set : Action >-> hSet.
Definition ac_type {G:gr} (X:Action G) := pr1hSet (ac_set X).
Definition ac_str {G:gr} (X:Action G) := pr2 X : ActionStructure G (ac_set X).
Definition ac_mult {G:gr} (X:Action G) := act_mult (pr2 X).
Delimit Scope action_scope with action.
Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Open Scope action_scope.
Definition ac_assoc {G:gr} (X:Action G) := act_assoc _ _ (pr2 X) : ∏ g h x, (op g h)*x = g*(h*x).

Definition right_mult {G:gr} {X:Action G} (x:X) := λ g, g*x.
Definition left_mult {G:gr} {X:Action G} (g:G) := λ x:X, g*x.

Definition is_equivariant {G:gr} {X Y:Action G} (f:X->Y) :=
  ∏ g x, f (g*x) = g*(f x).

Definition is_equivariant_isaprop {G:gr} {X Y:Action G} (f:X->Y) :
  isaprop (is_equivariant f).
Proof. intros. apply impred; intro g. apply impred; intro x.
       apply setproperty. Defined.

(** The following fact is fundamental: it shows that our definition of
    [is_equivariant] captures all of the structure.  The proof reduces to
    showing that if G acts on a set X in two ways, and the identity function is
    equivariant, then the two actions are equal.  A similar fact will hold in
    other cases: groups, rings, monoids, etc.  Refer to section 9.8 of the HoTT
    book, on the "structure identity principle", a term coined by Peter Aczel. *)

Definition is_equivariant_identity {G:gr} {X Y:Action G}
           (p:ac_set X = ac_set Y) :
  weq (p # ac_str X = ac_str Y) (is_equivariant (cast (ap pr1hSet p))).
Proof. intros ? [X [Xm Xu Xa]] [Y [Ym Yu Ya]] ? .
       (* should just apply hPropUnivalence at this point, as in Poset_univalence_prelim! *)
       simpl in p. destruct p; simpl. unfold transportf; simpl. unfold idfun; simpl.
       simple refine (weqpair _ _).
       { intros p g x. simpl in x. simpl.
         exact (eqtohomot (eqtohomot (ap act_mult p) g) x). }
       simple refine (gradth _ _ _ _).
       { unfold cast; simpl.
         intro i.
         assert (p:Xm=Ym).
         { apply funextsec; intro g. apply funextsec; intro x; simpl in x.
           exact (i g x). }
         destruct p. clear i. assert (p:Xu=Yu).
         { apply funextsec; intro x; simpl in x. apply setproperty. }
         destruct p. assert (p:Xa=Ya).
         { apply funextsec; intro g. apply funextsec; intro h.
           apply funextsec; intro x. apply setproperty. }
         destruct p. reflexivity. }
       { intro p. apply isaset_ActionStructure. }
       { intro is. apply is_equivariant_isaprop. } Defined.

Definition is_equivariant_comp {G:gr} {X Y Z:Action G}
           (p:X->Y) (i:is_equivariant p)
           (q:Y->Z) (j:is_equivariant q) : is_equivariant (funcomp p q).
Proof. intros. intros g x. exact (ap q (i g x) @ j g (p x)). Defined.

Definition ActionMap {G:gr} (X Y:Action G) := total2 (@is_equivariant _ X Y).

Definition underlyingFunction {G:gr} {X Y:Action G} (f:ActionMap X Y) := pr1 f.

Definition equivariance {G:gr} {X Y:Action G} (f:ActionMap X Y) := pr2 f.

Coercion underlyingFunction : ActionMap >-> Funclass.

Definition composeActionMap {G:gr} (X Y Z:Action G)
           (p:ActionMap X Y) (q:ActionMap Y Z) : ActionMap X Z.
Proof. intros ? ? ? ? [p i] [q j]. exists (funcomp p q).
       apply is_equivariant_comp. assumption. assumption. Defined.

Definition ActionIso {G:gr} (X Y:Action G) :=
  ∑ f:(ac_set X) ≃ (ac_set Y), is_equivariant f.

Definition underlyingIso {G:gr} {X Y:Action G} (e:ActionIso X Y) := pr1 e : X ≃ Y.

Coercion underlyingIso : ActionIso >-> weq.

Lemma underlyingIso_incl {G:gr} {X Y:Action G} :
  isincl (underlyingIso : ActionIso X Y -> X ≃ Y).
Proof. intros. apply isinclpr1; intro f. apply is_equivariant_isaprop. Defined.

Lemma underlyingIso_injectivity {G:gr} {X Y:Action G}
      (e f:ActionIso X Y) :
  (e = f) ≃ (underlyingIso e = underlyingIso f).
Proof. intros. apply weqonpathsincl. apply underlyingIso_incl. Defined.

Definition underlyingActionMap {G:gr} {X Y:Action G} (e:ActionIso X Y) :=
  pr1weq (pr1 e),, pr2 e.

Definition idActionIso {G:gr} (X:Action G) : ActionIso X X.
Proof. intros. exists (idweq _). intros g x. reflexivity. Defined.

Definition composeActionIso {G:gr} {X Y Z:Action G}
           (e:ActionIso X Y) (f:ActionIso Y Z) : ActionIso X Z.
Proof. intros ? ? ? ? [e i] [f j]. exists (weqcomp e f).
       destruct e as [e e'], f as [f f']; simpl.
       apply is_equivariant_comp. exact i. exact j. Defined.

Definition path_to_ActionIso {G:gr} {X Y:Action G} (e:X = Y) : ActionIso X Y.
Proof. intros. destruct e. exact (idActionIso X). Defined.

Definition castAction {G:gr} {X Y:Action G} (e:X = Y) : X -> Y.
Proof. intros ? ? ? ? x. exact (path_to_ActionIso e x). Defined.

(** ** Applications of univalence *)

Definition Action_univalence_prelim {G:gr} {X Y:Action G} :
  (X = Y) ≃ (ActionIso X Y).
Proof. intros.
       simple refine (weqcomp (total2_paths_equiv (ActionStructure G) X Y) _).
       simple refine (weqbandf _ _ _ _).
       { apply hSet_univalence. }
       simpl. intro p. simple refine (weqcomp (is_equivariant_identity p) _).
       exact (eqweqmap (ap is_equivariant (pr1_eqweqmap (ap pr1hSet p)))).
Defined.

Definition Action_univalence_prelim_comp {G:gr} {X Y:Action G} (p:X = Y) :
   Action_univalence_prelim p = path_to_ActionIso p.
Proof. intros. destruct p. apply (maponpaths (tpair _ _)). apply funextsec; intro g.
       apply funextsec; intro x. apply setproperty. Defined.

Lemma path_to_ActionIso_isweq {G:gr} {X Y:Action G}  :
   isweq (@path_to_ActionIso G X Y).
Proof. intros. exact (isweqhomot Action_univalence_prelim
                         path_to_ActionIso
                         Action_univalence_prelim_comp
                         (pr2 Action_univalence_prelim)). Qed.

Definition Action_univalence {G:gr} {X Y:Action G} :
  (X = Y) ≃ (ActionIso X Y).
Proof. intros. exists path_to_ActionIso. apply path_to_ActionIso_isweq. Defined.

Definition Action_univalence_comp {G:gr} {X Y:Action G} (p:X = Y) :
   Action_univalence p = path_to_ActionIso p.
Proof. reflexivity. Defined.

Definition Action_univalence_inv {G:gr} {X Y:Action G}
  : (ActionIso X Y) ≃ (X=Y) := invweq Action_univalence.

Definition Action_univalence_inv_comp {G:gr} {X Y:Action G} (f:ActionIso X Y) :
  path_to_ActionIso (Action_univalence_inv f) = f.
Proof. intros.
       unfold Action_univalence_inv, Action_univalence.
       apply (homotweqinvweq Action_univalence f). Defined.

Definition Action_univalence_inv_comp_eval {G:gr} {X Y:Action G} (f:ActionIso X Y) (x:X) :
  castAction (Action_univalence_inv f) x = f x.
Proof. intros. exact (eqtohomot
                        (ap pr1weq
                            (ap underlyingIso
                                (Action_univalence_inv_comp f)))
                        x). Defined.

(** ** Torsors *)

Definition is_torsor {G:gr} (X:Action G) :=
  nonempty X × ∏ x:X, isweq (right_mult x).

Lemma is_torsor_isaprop {G:gr} (X:Action G) : isaprop (is_torsor X).
Proof. intros. apply isapropdirprod. { apply propproperty. }
       { apply impred; intro x. apply isapropisweq. } Qed.

Definition Torsor (G:gr) := total2 (@is_torsor G).

Definition underlyingAction {G} (X:Torsor G) := pr1 X : Action G.
Coercion underlyingAction : Torsor >-> Action.
Definition is_torsor_prop {G} (X:Torsor G) := pr2 X.
Definition torsor_nonempty {G} (X:Torsor G) := pr1 (is_torsor_prop X).
Definition torsor_splitting {G} (X:Torsor G) := pr2 (is_torsor_prop X).
Definition torsor_mult_weq {G} (X:Torsor G) (x:X) :=
  weqpair (right_mult x) (torsor_splitting X x) : G ≃ X.
Definition torsor_update_nonempty {G} (X:Torsor G) (x:nonempty X) : Torsor G.
Proof. intros ? X new.
       exact (underlyingAction X,,(new,,pr2(is_torsor_prop X))). Defined.
Definition castTorsor {G} {T T':Torsor G} (q:T = T') : T -> T'.
Proof. intros ? ? ? ?. exact (castAction (ap underlyingAction q)). Defined.

Lemma underlyingAction_incl {G:gr} :
  isincl (underlyingAction : Torsor G -> Action G).
Proof. intros. refine (isinclpr1 _ _); intro X. apply is_torsor_isaprop. Defined.

Lemma underlyingAction_injectivity {G:gr} {X Y:Torsor G} :
      (X = Y) ≃ (underlyingAction X = underlyingAction Y).
Proof. intros. apply weqonpathsincl. apply underlyingAction_incl. Defined.

Definition underlyingAction_injectivity_comp {G:gr} {X Y:Torsor G} (p:X = Y) :
  underlyingAction_injectivity p = ap underlyingAction p.
Proof. reflexivity. Defined.

Definition underlyingAction_injectivity_comp' {G:gr} {X Y:Torsor G} :
     pr1weq (@underlyingAction_injectivity G X Y)
  = @ap (Torsor G) (Action G) (@underlyingAction G) X Y.
Proof. reflexivity. Defined.

Definition underlyingAction_injectivity_inv_comp {G:gr} {X Y:Torsor G}
           (f:underlyingAction X = underlyingAction Y) :
  ap underlyingAction (invmap underlyingAction_injectivity f) = f.
Proof. intros. apply (homotweqinvweq underlyingAction_injectivity f). Defined.

Definition PointedTorsor (G:gr) := ∑ X:Torsor G, X.
Definition underlyingTorsor {G} (X:PointedTorsor G) := pr1 X : Torsor G.
Coercion underlyingTorsor : PointedTorsor >-> Torsor.
Definition underlyingPoint {G} (X:PointedTorsor G) := pr2 X : X.

Lemma is_quotient {G} (X:Torsor G) (y x:X) : ∃! g, g*x = y.
Proof. intros. exact (pr2 (is_torsor_prop X) x y). Defined.

Definition quotient {G} (X:Torsor G) (y x:X) := pr1 (thePoint (is_quotient X y x)) : G.
Local Notation "y / x" := (quotient _ y x) : action_scope.

Lemma quotient_times {G} (X:Torsor G) (y x:X) : (y/x)*x = y.
Proof. intros. exact (pr2 (thePoint (is_quotient _ y x))). Defined.

Lemma quotient_uniqueness {G} (X:Torsor G) (y x:X) (g:G) : g*x = y -> g = y/x.
Proof. intros ? ? ? ? ? e.
       exact (ap pr1 (uniqueness (is_quotient _ y x) (g,,e))). Defined.

Lemma quotient_mult {G} (X:Torsor G) (g:G) (x:X) : (g*x)/x = g.
Proof. intros. apply pathsinv0. apply quotient_uniqueness. reflexivity. Defined.

Lemma quotient_1 {G} (X:Torsor G) (x:X) : x/x = 1%multmonoid.
Proof. intros. apply pathsinv0. apply quotient_uniqueness. apply act_unit.
Defined.

Lemma quotient_product {G} (X:Torsor G) (z y x:X) : op (z/y) (y/x) = z/x.
Proof. intros. apply quotient_uniqueness.
       exact (ac_assoc _ _ _ _
            @ ap (left_mult (z/y)) (quotient_times _ y x)
            @ quotient_times _ z y). Defined.

Definition trivialTorsor (G:gr) : Torsor G.
Proof.
  intros. exists (makeAction G (make G G op (lunax G) (assocax G))).
  exact (hinhpr (unel G),,
         λ x, gradth
           (λ g, op g x)
           (λ g, op g (grinv _ x))
           (λ g, assocax _ g x (grinv _ x) @ ap (op g) (grrinvax G x) @ runax _ g)
           (λ g, assocax _ g (grinv _ x) x @ ap (op g) (grlinvax G x) @ runax _ g)).
Defined.

Definition pointedTrivialTorsor (G:gr) : PointedTorsor G.
Proof. intros. exists (trivialTorsor G). exact (unel G). Defined.

Definition univ_function {G:gr} (X:Torsor G) (x:X) : trivialTorsor G -> X.
Proof. intros ? ? ?. apply right_mult. assumption. Defined.

Definition univ_function_pointed {G:gr} (X:Torsor G) (x:X) :
  univ_function X x (unel _) = x.
Proof. intros. apply act_unit. Defined.

Definition univ_function_is_equivariant {G:gr} (X:Torsor G) (x:X) :
  is_equivariant (univ_function X x).
Proof. intros. intros g h. apply act_assoc. Defined.

Definition triviality_isomorphism {G:gr} (X:Torsor G) (x:X) :
  ActionIso (trivialTorsor G) X.
Proof. intros.
       exact (torsor_mult_weq X x,, univ_function_is_equivariant X x). Defined.

Definition trivialTorsor_weq (G:gr) (g:G) : (trivialTorsor G) ≃ (trivialTorsor G).
Proof. intros. exists (λ h, op h g). apply (gradth _ (λ h, op h (grinv G g))).
       { exact (λ h, assocax _ _ _ _ @ ap (op _) (grrinvax _ _) @ runax _ _). }
       { exact (λ h, assocax _ _ _ _ @ ap (op _) (grlinvax _ _) @ runax _ _). }
Defined.

Definition trivialTorsorAuto (G:gr) (g:G) :
  ActionIso (trivialTorsor G) (trivialTorsor G).
Proof. intros. exists (trivialTorsor_weq G g).
       intros h x. simpl.  exact (assocax _ h x g). Defined.

Lemma pr1weq_injectivity {X Y} (f g:X ≃ Y) : (f = g) ≃ (pr1weq f = pr1weq g).
Proof. intros. apply weqonpathsincl. apply isinclpr1weq.  Defined.

Definition autos (G:gr) : G ≃ (ActionIso (trivialTorsor G) (trivialTorsor G)).
Proof. intros. exists (trivialTorsorAuto G). simple refine (gradth _ _ _ _).
       { intro f. exact (f (unel G)). } { intro g; simpl. exact (lunax _ g). }
       { intro f; simpl. apply (invweq (underlyingIso_injectivity _ _)); simpl.
         apply (invweq (pr1weq_injectivity _ _)). apply funextsec; intro g.
         simpl. exact ((! (pr2 f) g (unel G)) @ (ap (pr1 f) (runax G g))).
       } Defined.

Definition autos_comp (G:gr) (g:G) :
  underlyingIso (autos G g) = trivialTorsor_weq G g.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Definition autos_comp_apply (G:gr) (g h:G) :
  (autos _ g) h = (h * g)%multmonoid.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Lemma trivialTorsorAuto_unit (G:gr) :
  trivialTorsorAuto G (unel _) = idActionIso _.
Proof. intros. simple refine (subtypeEquality _ _).
       { intro k. apply is_equivariant_isaprop. }
       { simple refine (subtypeEquality _ _).
         { intro; apply isapropisweq. }
         { apply funextsec; intro x; simpl. exact (runax G x). } }
Defined.

Lemma trivialTorsorAuto_mult (G:gr) (g h:G) :
  composeActionIso (trivialTorsorAuto G g) (trivialTorsorAuto G h)
  = (trivialTorsorAuto G (op g h)).
Proof. intros. simple refine (subtypeEquality _ _).
       { intro; apply is_equivariant_isaprop. }
       { simple refine (subtypeEquality _ _).
         { intro; apply isapropisweq. }
         { apply funextsec; intro x; simpl. exact (assocax _ x g h). } }
Defined.

(** ** Applications of univalence *)

Definition Torsor_univalence {G:gr} {X Y:Torsor G} : (X = Y) ≃ (ActionIso X Y).
Proof. intros. simple refine (weqcomp underlyingAction_injectivity _).
       apply Action_univalence. Defined.

Definition Torsor_univalence_comp {G:gr} {X Y:Torsor G} (p:X = Y) :
   Torsor_univalence p = path_to_ActionIso (ap underlyingAction p).
Proof. reflexivity. Defined.

Definition Torsor_univalence_inv_comp_eval {G:gr} {X Y:Torsor G}
           (f:ActionIso X Y) (x:X) :
  castTorsor (invmap Torsor_univalence f) x = f x.
Proof. intros. unfold Torsor_univalence.
       unfold castTorsor. rewrite invmapweqcomp. unfold weqcomp; simpl.
       rewrite underlyingAction_injectivity_inv_comp.
       apply Action_univalence_inv_comp_eval. Defined.

Definition torsor_eqweq_to_path {G:gr} {X Y:Torsor G} : ActionIso X Y -> X = Y.
Proof. intros ? ? ? f. exact ((invweq Torsor_univalence) f). Defined.

Definition PointedActionIso {G:gr} (X Y:PointedTorsor G)
    := ∑ f:ActionIso X Y, f (underlyingPoint X) = underlyingPoint Y.

Definition pointed_triviality_isomorphism {G:gr} (X:PointedTorsor G) :
  PointedActionIso (pointedTrivialTorsor G) X.
Proof. intros ? [X x]. exists (triviality_isomorphism X x).
       simpl. apply univ_function_pointed. Defined.

Definition PointedTorsor_univalence {G:gr} {X Y:PointedTorsor G} :
  (X = Y) ≃ (PointedActionIso X Y).
Proof. intros.
       simple refine (weqcomp (total2_paths_equiv _ X Y) _).
       simple refine (weqbandf _ _ _ _).
       { intros.
         exact (weqcomp (weqonpathsincl underlyingAction underlyingAction_incl X Y)
                        Action_univalence). }
       destruct X as [X x], Y as [Y y]; simpl. intro p. destruct p; simpl.
       exact (idweq _). Defined.

Definition ClassifyingSpace G := pointedType (Torsor G) (trivialTorsor G).
Definition E := PointedTorsor.
Definition B := ClassifyingSpace.
Definition π {G:gr} := underlyingTorsor : E G -> B G.

Lemma isconnBG (G:gr) : isconnected (B G).
Proof. intros. apply (base_connected (trivialTorsor _)).
  intros X. apply (squash_to_prop (torsor_nonempty X)). { apply propproperty. }
  intros x. apply hinhpr. exact (torsor_eqweq_to_path (triviality_isomorphism X x)).
Defined.

Lemma iscontrEG (G:gr) : iscontr (E G).
Proof. intros. exists (pointedTrivialTorsor G). intros [X x].
       apply pathsinv0. apply (invweq PointedTorsor_univalence).
       apply pointed_triviality_isomorphism. Defined.

Theorem loopsBG (G:gr) : weq (Ω (B G)) G.
Proof. intros. apply invweq.
       simple refine (weqcomp _ (invweq Torsor_univalence)).
       apply autos. Defined.

Definition loopsBG_comp (G:gr) (g h:G)
  : castTorsor (invmap (loopsBG G) g) h = (h*g)%multmonoid.
Proof. intros. unfold loopsBG. rewrite invinv. unfold weqcomp; simpl.
       rewrite (Torsor_univalence_inv_comp_eval (trivialTorsorAuto G g)).
       reflexivity. Defined.

(** Theorem [loopsBG] also follows from the Rezk Completion theorem of the CategoryTheory
    package.  To see that, regard G as a category with one object.  Consider a
    merely representable functor F : G^op -> Set.  Let X be F of the object *.
    Apply F to the arrows to get an action of G on X.  Try to prove that X is a
    torsor.  Since being a torsor is a mere property, we may assume F is
    actually representable.  There is only one object *, so F is isomorphic to
    h_*.  Apply h_* to * and we get Hom(*,*), which is G, regarded as a G-set.
    That's a torsor.  So the Rezk completion RCG is equivalent to BG, the type
    of G-torsors.  Now the theorem also says there is an equivalence G -> RCG.
    So RCG is connected and its loop space is G.

    A formalization of that argument should be added eventually. *)

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/GroupAction.vo"
End:
*)
