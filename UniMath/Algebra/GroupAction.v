(* -*- coding: utf-8 *)

(** * Group actions *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Combinatorics.OrderedSets.

(** ** Definitions *)

Definition action_op G (X:hSet) : Type := ∏ (g:G) (x:X), X.

Section A.
  Context (G:gr) (X:hSet).
  Definition ActionStructure : Type :=
    ∑ (act_mult  :    action_op G X)
      (act_unit  :    ∏ x, act_mult (unel G) x = x),
   (*  act_assoc : *) ∏ g h x, act_mult (op g h) x = act_mult g (act_mult h x).
  Definition make act_mult act_unit act_assoc : ActionStructure := act_mult,, act_unit,, act_assoc.
  Definition act_mult (x:ActionStructure) := pr1 x.
  Definition act_unit (x:ActionStructure) := pr12 x.
  Definition act_assoc (x:ActionStructure) := pr22 x.
End A.
Arguments act_mult {_ _} _ _ _.

Lemma isaset_ActionStructure (G:gr) (X:hSet) : isaset (ActionStructure G X).
Proof.
  intros.
  apply isaset_total2.
  { apply (impred 2); intro g. apply impred; intro x. apply setproperty. }
  intro op.
  apply isaset_total2.
  { apply (impred 2); intro x. apply hlevelntosn. apply setproperty. }
  intro un. apply (impred 2); intro g. apply (impred 2); intro h. apply (impred 2); intro x.
  apply hlevelntosn. apply setproperty.
Qed.

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
Local Open Scope action_scope.
Definition ac_assoc {G:gr} (X:Action G) := act_assoc _ _ (pr2 X) : ∏ g h x, (op g h)*x = g*(h*x).

Definition right_mult {G:gr} {X:Action G} (x:X) := λ g, g*x.
Definition left_mult {G:gr} {X:Action G} (g:G) := λ x:X, g*x.

Definition is_equivariant {G:gr} {X Y:Action G} (f:X->Y) : hProp :=
  (∀ g x, f (g*x) = g*(f x))%set.

Definition is_equivariant_isaprop {G:gr} {X Y:Action G} (f:X->Y) :
  isaprop (is_equivariant f).
Proof.
  apply propproperty.
Defined.

(** The following fact is fundamental: it shows that our definition of
    [is_equivariant] captures all of the structure.  The proof reduces to
    showing that if G acts on a set X in two ways, and the identity function is
    equivariant, then the two actions are equal.  A similar fact will hold in
    other cases: groups, rings, monoids, etc.  Refer to section 9.8 of the HoTT
    book, on the "structure identity principle", a term coined by Peter Aczel. *)
Local Open Scope transport.

Definition is_equivariant_identity {G:gr} {X Y:Action G}
           (p:ac_set X = ac_set Y) :
  weq (p # ac_str X = ac_str Y) (is_equivariant (cast (maponpaths pr1hSet p))).
Proof.
  revert X Y p; intros [X [Xm [Xu Xa]]] [Y [Ym [Yu Ya]]] ? .
  (* should just apply hPropUnivalence at this point, as in Poset_univalence_prelim! *)
  simpl in p. destruct p; simpl. unfold transportf; simpl. unfold idfun; simpl.
  simple refine (weqpair _ _).
  { intros p g x. simpl in x. simpl.
    exact (eqtohomot (eqtohomot (maponpaths act_mult p) g) x). }
  simple refine (isweq_iso _ _ _ _).
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
  { intro is. apply proofirrelevance.
    apply impred; intros g.
    apply impred; intros x.
    apply setproperty. }
Defined.

Definition is_equivariant_comp {G:gr} {X Y Z:Action G}
           (p:X->Y) (i:is_equivariant p)
           (q:Y->Z) (j:is_equivariant q) : is_equivariant (funcomp p q).
Proof.
  intros. intros g x. exact (maponpaths q (i g x) @ j g (p x)).
Defined.

Definition ActionMap {G:gr} (X Y:Action G) := total2 (@is_equivariant _ X Y).

Definition underlyingFunction {G:gr} {X Y:Action G} (f:ActionMap X Y) := pr1 f.

Coercion underlyingFunction : ActionMap >-> Funclass.

Definition equivariance {G:gr} {X Y:Action G} (f:ActionMap X Y) : is_equivariant f
  := pr2 f.

Definition composeActionMap {G:gr} (X Y Z:Action G)
           (p:ActionMap X Y) (q:ActionMap Y Z) : ActionMap X Z.
Proof.
  revert p q; intros [p i] [q j]. exists (funcomp p q).
  apply is_equivariant_comp. assumption. assumption.
Defined.

Definition ActionIso {G:gr} (X Y:Action G) : Type.
Proof.
  exact  (∑ f:(ac_set X) ≃ (ac_set Y), is_equivariant f).
Defined.

Lemma ActionIso_isaset {G:gr} (X Y:Action G) : isaset (ActionIso X Y).
Proof.
  apply (isofhlevelsninclb _ pr1).
  { apply isinclpr1; intro f. apply propproperty. }
  apply isofhlevelsnweqtohlevelsn.
  apply setproperty.
Defined.

Coercion underlyingIso {G:gr} {X Y:Action G} (e:ActionIso X Y) : X ≃ Y := pr1 e.

Lemma underlyingIso_incl {G:gr} {X Y:Action G} :
  isincl (underlyingIso : ActionIso X Y -> X ≃ Y).
Proof.
  intros. apply isinclpr1; intro f. apply propproperty.
Defined.

Local Goal ∏ G (X Y:Action G) (i : ActionIso X Y) (x:X), Y.
  intros.
  exact (i x).
Qed.

Lemma underlyingIso_injectivity {G:gr} {X Y:Action G}
      (e f:ActionIso X Y) :
  (e = f) ≃ (underlyingIso e = underlyingIso f).
Proof.
  intros. apply weqonpathsincl. apply underlyingIso_incl.
Defined.

Definition underlyingActionMap {G:gr} {X Y:Action G} (e:ActionIso X Y) : ActionMap X Y :=
  pr1weq (pr1 e),, pr2 e.

Definition idActionIso {G:gr} (X:Action G) : ActionIso X X.
Proof.
  intros. exists (idweq _). intros g x. reflexivity.
Defined.

Definition composeActionIso {G:gr} {X Y Z:Action G}
           (e:ActionIso X Y) (f:ActionIso Y Z) : ActionIso X Z.
Proof.
  revert e f; intros [e i] [f j]. exists (weqcomp e f).
  destruct e as [e e'], f as [f f']; simpl.
  apply is_equivariant_comp. exact i. exact j.
Defined.

Lemma composeActionIsoId {G:gr} {X Y:Action G} (f : ActionIso X Y) : composeActionIso (idActionIso X) f = f.
Proof.
  apply subtypeEquality.
  { intros g. apply propproperty. }
  apply subtypeEquality.
  { intros g. apply isapropisweq. }
  reflexivity.
Defined.

Lemma composeActionIsoId' {G:gr} {X Y:Action G} (f : ActionIso X Y) : composeActionIso f (idActionIso Y) = f.
Proof.
  apply subtypeEquality.
  { intros g. apply propproperty. }
  apply subtypeEquality.
  { intros g. apply isapropisweq. }
  reflexivity.
Defined.

Definition path_to_ActionIso {G:gr} {X Y:Action G} (e:X = Y) : ActionIso X Y.
Proof.
  intros. destruct e. exact (idActionIso X).
Defined.

Definition castAction {G:gr} {X Y:Action G} (e:X = Y) : X -> Y.
Proof.
  intros x. exact (path_to_ActionIso e x).
Defined.

(** ** Applications of univalence *)

Definition Action_univalence_prelim {G:gr} {X Y:Action G} :
  (X = Y) ≃ (ActionIso X Y).
Proof.
  intros.
  simple refine (weqcomp (total2_paths_equiv (ActionStructure G) X Y) _).
  simple refine (weqbandf _ _ _ _).
  { apply hSet_univalence. }
  simpl. intro p. simple refine (weqcomp (is_equivariant_identity p) _).
  exact (eqweqmap (maponpaths (λ f, hProptoType (is_equivariant f)) (pr1_eqweqmap (maponpaths pr1hSet p)))).
Defined.

Definition Action_univalence_prelim_comp {G:gr} {X Y:Action G} (p:X = Y) :
   Action_univalence_prelim p = path_to_ActionIso p.
Proof.
  intros. destruct p. apply (maponpaths (tpair _ _)). apply funextsec; intro g.
  apply funextsec; intro x. apply setproperty.
Defined.

Lemma path_to_ActionIsweq_iso {G:gr} {X Y:Action G}  :
   isweq (@path_to_ActionIso G X Y).
Proof.
  intros. exact (isweqhomot Action_univalence_prelim
                            path_to_ActionIso
                            Action_univalence_prelim_comp
                            (pr2 Action_univalence_prelim)).
Qed.

Definition Action_univalence {G:gr} {X Y:Action G} :
  (X = Y) ≃ (ActionIso X Y).
Proof.
  intros. exists path_to_ActionIso. apply path_to_ActionIsweq_iso.
Defined.

Definition Action_univalence_comp {G:gr} {X Y:Action G} (p:X = Y) :
   Action_univalence p = path_to_ActionIso p.
Proof.
  reflexivity.
Defined.

Definition Action_univalence_inv {G:gr} {X Y:Action G}
  : (ActionIso X Y) ≃ (X=Y) := invweq Action_univalence.

Definition Action_univalence_inv_comp {G:gr} {X Y:Action G} (f:ActionIso X Y) :
  path_to_ActionIso (Action_univalence_inv f) = f.
Proof.
  intros.
  unfold Action_univalence_inv, Action_univalence.
  apply (homotweqinvweq Action_univalence f).
Defined.

Definition Action_univalence_inv_comp_eval {G:gr} {X Y:Action G} (f:ActionIso X Y) (x:X) :
  castAction (Action_univalence_inv f) x = f x.
Proof.
  intros. exact (eqtohomot
                   (maponpaths pr1weq
                               (maponpaths underlyingIso
                                           (Action_univalence_inv_comp f)))
                   x).
Defined.

(** ** Torsors *)

Definition is_torsor {G:gr} (X:Action G) :=
  nonempty X × ∏ x:X, isweq (right_mult x).

Lemma is_torsor_isaprop {G:gr} (X:Action G) : isaprop (is_torsor X).
Proof.
  intros. apply isapropdirprod.
  { apply propproperty. }
  { apply impred; intro x. apply isapropisweq. }
Qed.

Definition Torsor (G:gr) := total2 (@is_torsor G).

Definition underlyingAction {G} (X:Torsor G) := pr1 X : Action G.
Coercion underlyingAction : Torsor >-> Action.
Definition is_torsor_prop {G} (X:Torsor G) := pr2 X.
Definition torsor_nonempty {G} (X:Torsor G) := pr1 (is_torsor_prop X).
Definition torsor_splitting {G} (X:Torsor G) := pr2 (is_torsor_prop X).
Definition torsor_mult_weq {G} (X:Torsor G) (x:X) :=
  weqpair (right_mult x) (torsor_splitting X x) : G ≃ X.
Definition torsor_mult_weq' {G} (X:Torsor G) (g:G) : X ≃ X.
Proof.
  exists (left_mult g).
  use isweq_iso.
    - exact (left_mult (grinv G g)).
    - intros x. unfold left_mult.
      intermediate_path ((grinv G g * g)%multmonoid * x).
      + apply pathsinv0,act_assoc.
      + intermediate_path (unel G * x).
        * apply (maponpaths (right_mult x)). apply grlinvax.
        * apply act_unit.
    - intros x. unfold left_mult.
      intermediate_path ((g * grinv G g)%multmonoid * x).
      + apply pathsinv0,act_assoc.
      + intermediate_path (unel G * x).
        * apply (maponpaths (right_mult x)). apply grrinvax.
        * apply act_unit.
Defined.
Definition left_mult_Iso {G:abgr} (X:Torsor G) (g:G) : ActionIso X X.
Proof.
  exists (torsor_mult_weq' X g). intros h x.
  change (g * (h * x) = h * (g * x)).
  refine (! ac_assoc X g h x @ _ @ ac_assoc X h g x).
  exact (maponpaths (right_mult x) (commax G g h)).
Defined.
Definition torsor_update_nonempty {G} (X:Torsor G) (x:nonempty X) : Torsor G.
Proof.
  exact (underlyingAction X,,(x,,pr2(is_torsor_prop X))).
Defined.
Definition castTorsor {G} {T T':Torsor G} (q:T = T') : T -> T'.
Proof.
  exact (castAction (maponpaths underlyingAction q)).
Defined.
Lemma castTorsor_transportf {G} {T T':Torsor G} (q:T = T') (t:T) :
  transportf (λ S, underlyingAction S) q t = castTorsor q t.
Proof.
  now induction q.
Defined.
Lemma underlyingAction_incl {G:gr} :
  isincl (underlyingAction : Torsor G -> Action G).
Proof.
  intros. refine (isinclpr1 _ _); intro X. apply is_torsor_isaprop.
Defined.

Lemma underlyingAction_injectivity {G:gr} {X Y:Torsor G} :
      (X = Y) ≃ (underlyingAction X = underlyingAction Y).
Proof.
  intros. apply weqonpathsincl. apply underlyingAction_incl.
Defined.

Definition underlyingAction_injectivity_comp {G:gr} {X Y:Torsor G} (p:X = Y) :
  underlyingAction_injectivity p = maponpaths underlyingAction p.
Proof.
  reflexivity.
Defined.

Definition underlyingAction_injectivity_comp' {G:gr} {X Y:Torsor G} :
     pr1weq (@underlyingAction_injectivity G X Y)
  = @maponpaths (Torsor G) (Action G) (@underlyingAction G) X Y.
Proof.
  reflexivity.
Defined.

Definition underlyingAction_injectivity_inv_comp {G:gr} {X Y:Torsor G}
           (f:underlyingAction X = underlyingAction Y) :
  maponpaths underlyingAction (invmap underlyingAction_injectivity f) = f.
Proof.
  intros. apply (homotweqinvweq underlyingAction_injectivity f).
Defined.

Definition PointedTorsor (G:gr) := ∑ X:Torsor G, X.
Definition underlyingTorsor {G} (X:PointedTorsor G) := pr1 X : Torsor G.
Coercion underlyingTorsor : PointedTorsor >-> Torsor.
Definition underlyingPoint {G} (X:PointedTorsor G) := pr2 X : X.

Lemma is_quotient {G} (X:Torsor G) (y x:X) : ∃! g, g*x = y.
Proof.
  intros. exact (pr2 (is_torsor_prop X) x y).
Defined.

Definition quotient {G} (X:Torsor G) (y x:X) := pr1 (iscontrpr1 (is_quotient X y x)) : G.
Local Notation "y / x" := (quotient _ y x) : action_scope.

Lemma quotient_times {G} {X:Torsor G} (y x:X) : (y/x)*x = y.
Proof.
  intros. exact (pr2 (iscontrpr1 (is_quotient _ y x))).
Defined.

Lemma quotient_uniqueness {G} {X:Torsor G} (y x:X) (g:G) : g*x = y -> g = y/x.
Proof.
  intros e.
  exact (maponpaths pr1 (uniqueness (is_quotient _ y x) (g,,e))).
Defined.

Lemma quotient_mult {G} (X:Torsor G) (g:G) (x:X) : (g*x)/x = g.
Proof.
  intros. apply pathsinv0. apply quotient_uniqueness. reflexivity.
Defined.

Lemma quotient_1 {G} (X:Torsor G) (x:X) : x/x = 1%multmonoid.
Proof.
  intros. apply pathsinv0. apply quotient_uniqueness. apply act_unit.
Defined.

Lemma quotient_product {G} (X:Torsor G) (z y x:X) : op (z/y) (y/x) = z/x.
Proof.
  intros. apply quotient_uniqueness.
  exact (ac_assoc _ _ _ _
                  @ maponpaths (left_mult (z/y)) (quotient_times y x)
                  @ quotient_times z y).
Defined.

Lemma quotient_map {G} {X Y:Torsor G} (f : ActionMap X Y) (x x':X) : f x' / f x = x' / x.
Proof.
  refine (! (quotient_uniqueness (f x') (f x) (x' / x) _)).
  assert (p := equivariance f (x'/x) x).
  refine (!p @ _); clear p.
  apply maponpaths.
  apply quotient_times.
Qed.

Lemma torsorMapIsIso {G} {X Y : Torsor G} (f : ActionMap X Y) : isweq f.
Proof.
  apply (squash_to_prop (torsor_nonempty X)).
  - apply isapropisweq.
  - intros x.
    set (y := f x).
    set (f' := λ y', y' / y * x).
    apply (isweq_iso f f').
    + intros x'.
      unfold f', y.
      assert (p := quotient_times x' x).
      refine (_ @ p); clear p.
      apply (maponpaths (λ g, g * x)).
      apply quotient_map.
    + intros y'.
      unfold f'.
      assert (p := equivariance f (y'/y) x).
      refine (p @ _); clear p.
      fold y.
      apply quotient_times.
Defined.

Definition torsorMap_to_torsorIso {G} {X Y : Torsor G} (f : ActionMap X Y) : ActionIso X Y.
Proof.
  use tpair.
  - exists f. apply torsorMapIsIso.
  - simpl. apply equivariance.
Defined.

Definition trivialTorsor (G:gr) : Torsor G.
Proof.
  intros. exists (makeAction G (make G G op (lunax G) (assocax G))).
  exact (hinhpr (unel G),,
         λ x, isweq_iso
           (λ g, op g x)
           (λ g, op g (grinv _ x))
           (λ g, assocax _ g x (grinv _ x) @ maponpaths (op g) (grrinvax G x) @ runax _ g)
           (λ g, assocax _ g (grinv _ x) x @ maponpaths (op g) (grlinvax G x) @ runax _ g)).
Defined.

Definition toTrivialTorsor {G:gr} (g:G) : trivialTorsor G.
Proof.
  exact g.
Defined.

Definition pointedTrivialTorsor (G:gr) : PointedTorsor G.
Proof.
  intros. exists (trivialTorsor G). exact (unel G).
Defined.

Definition univ_function {G:gr} (X:Torsor G) (x:X) : trivialTorsor G -> X.
Proof.
  apply right_mult. assumption.
Defined.

Definition univ_function_pointed {G:gr} (X:Torsor G) (x:X) :
  univ_function X x (unel _) = x.
Proof.
  intros. apply act_unit.
Defined.

Definition univ_function_is_equivariant {G:gr} (X:Torsor G) (x:X) :
  is_equivariant (univ_function X x).
Proof.
  intros. intros g h. apply act_assoc.
Defined.

Definition triviality_isomorphism {G:gr} (X:Torsor G) (x:X) :
  ActionIso (trivialTorsor G) X.
Proof.
  intros.
  exact (torsor_mult_weq X x,, univ_function_is_equivariant X x).
Defined.

Lemma triviality_isomorphism_compute (G:gr) :
  triviality_isomorphism (trivialTorsor G) (unel G) = idActionIso (trivialTorsor G).
Proof.
  apply subtypeEquality_prop.
  apply subtypeEquality.
  { intros X. apply isapropisweq. }
  apply funextsec; intros g.
  change (op g (unel _) = g).
  apply runax.
Defined.

Definition trivialTorsor_weq (G:gr) (g:G) : (trivialTorsor G) ≃ (trivialTorsor G).
Proof.
  intros. exists (λ h, op h g). apply (isweq_iso _ (λ h, op h (grinv G g))).
  { exact (λ h, assocax _ _ _ _ @ maponpaths (op _) (grrinvax _ _) @ runax _ _). }
  { exact (λ h, assocax _ _ _ _ @ maponpaths (op _) (grlinvax _ _) @ runax _ _). }
Defined.

Definition trivialTorsorAuto (G:gr) (g:G) :
  ActionIso (trivialTorsor G) (trivialTorsor G).
Proof.
  intros. exists (trivialTorsor_weq G g).
  intros h x. simpl.  exact (assocax _ h x g).
Defined.

Lemma pr1weq_injectivity {X Y} (f g:X ≃ Y) : (f = g) ≃ (pr1weq f = pr1weq g).
Proof.
  intros. apply weqonpathsincl. apply isinclpr1weq.
Defined.

Definition trivialTorsorRightMultiplication (G:gr) : G ≃ ActionIso (trivialTorsor G) (trivialTorsor G).
Proof.
  exists (trivialTorsorAuto G). simple refine (isweq_iso _ _ _ _).
  { intro f. exact (f (unel G)). }
  { intro g; simpl. exact (lunax _ g). }
  { intro f; simpl. apply (invweq (underlyingIso_injectivity _ _)); simpl.
    apply (invweq (pr1weq_injectivity _ _)). apply funextsec; intro g.
    simpl. exact ((! (pr2 f) g (unel G)) @ (maponpaths (pr1 f) (runax G g))). }
Defined.

Definition autos_comp (G:gr) (g:G) :
  underlyingIso (trivialTorsorRightMultiplication G g) = trivialTorsor_weq G g.
Proof.
  reflexivity.             (* don't change the proof *)
Defined.

Definition autos_comp_apply (G:gr) (g h:G) :
  (trivialTorsorRightMultiplication _ g) h = (h * g)%multmonoid.
Proof.
  reflexivity.             (* don't change the proof *)
Defined.

Lemma trivialTorsorAuto_unit (G:gr) :
  trivialTorsorAuto G (unel _) = idActionIso _.
Proof.
  intros. simple refine (subtypeEquality _ _).
  { intro k. apply is_equivariant_isaprop. }
  { simple refine (subtypeEquality _ _).
    { intro; apply isapropisweq. }
    { apply funextsec; intro x; simpl. exact (runax G x). } }
Defined.

Lemma trivialTorsorAuto_mult (G:gr) (g h:G) :
  composeActionIso (trivialTorsorAuto G g) (trivialTorsorAuto G h)
  = (trivialTorsorAuto G (op g h)).
Proof.
  intros. simple refine (subtypeEquality _ _).
  { intro; apply is_equivariant_isaprop. }
  { simple refine (subtypeEquality _ _).
    { intro; apply isapropisweq. }
    { apply funextsec; intro x; simpl. exact (assocax _ x g h). } }
Defined.

(** ** Applications of univalence *)

Definition torsor_univalence {G:gr} {X Y:Torsor G} : (X = Y) ≃ (ActionIso X Y).
Proof.
  intros. simple refine (weqcomp underlyingAction_injectivity _).
  apply Action_univalence.
Defined.

Corollary torsor_hlevel {G:gr} : isofhlevel 3 (Torsor G).
Proof.
  intros X Y.
  apply (isofhlevelweqb 2 torsor_univalence).
  apply ActionIso_isaset.
Defined.

Definition torsor_univalence_comp {G:gr} {X Y:Torsor G} (p:X = Y) :
   torsor_univalence p = path_to_ActionIso (maponpaths underlyingAction p).
Proof.
  reflexivity.
Defined.

Definition torsor_univalence_inv_comp_eval {G:gr} {X Y:Torsor G}
           (f:ActionIso X Y) (x:X) :
  castTorsor (invmap torsor_univalence f) x = f x.
Proof.
  intros. unfold torsor_univalence.
  unfold castTorsor. rewrite invmapweqcomp. (* too slow *)
  unfold weqcomp; simpl.
  rewrite underlyingAction_injectivity_inv_comp.
  apply Action_univalence_inv_comp_eval.
Defined.

Definition torsor_eqweq_to_path {G:gr} {X Y:Torsor G} : ActionIso X Y -> X = Y.
Proof.
  intros f. exact (invweq torsor_univalence f).
Defined.

Definition torsorMap_to_path {G:gr} {X Y:Torsor G} : ActionMap X Y -> X = Y.
Proof.
  intros f.
  apply (invweq torsor_univalence).
  apply torsorMap_to_torsorIso.
  exact f.
Defined.

Theorem TorsorIso_rect {G:gr} {X Y : Torsor G} (P : ActionIso X Y -> UU) :
  (∏ e : X = Y, P (torsor_univalence e)) -> ∏ f, P f.
Proof.
  intros ih ?.
  set (p := ih (invmap torsor_univalence f)).
  set (h := homotweqinvweq torsor_univalence f).
  exact (transportf P h p).
Defined.

Ltac torsor_induction f e :=
  generalize f; apply TorsorIso_rect; intro e; clear f.

Theorem TorsorIso_rect' {G:gr} {X : Torsor G} (P : ∏ Y : Torsor G, ActionIso X Y -> Type) :
  P X (idActionIso X) -> ∏ (Y : Torsor G) (f:ActionIso X Y), P Y f.
Proof.
  intros p ? ?. torsor_induction f q. induction q. exact p.
Defined.

Ltac torsor_induction' f X :=
  generalize f; generalize X; apply TorsorIso_rect'; clear f X.

Lemma torsor_univalence_id {G:gr} (X:Torsor G) : invmap torsor_univalence (idActionIso X) = idpath X.
(* upstream *)
Proof.
  change (idActionIso X) with (torsor_univalence (idpath X)).
  apply homotinvweqweq.
Defined.

Definition invUnivalenceCompose {G:gr} {X Y Z : Torsor G} (f : ActionIso X Y) (g : ActionIso Y Z) :
  invmap torsor_univalence f @ invmap torsor_univalence g = invmap torsor_univalence (composeActionIso f g).
Proof.
  torsor_induction' g Z. rewrite composeActionIsoId'. rewrite torsor_univalence_id. apply pathscomp0rid.
Defined.

Definition PointedActionIso {G:gr} (X Y:PointedTorsor G)
    := ∑ f:ActionIso X Y, f (underlyingPoint X) = underlyingPoint Y.

Definition pointed_triviality_isomorphism {G:gr} (X:PointedTorsor G) :
  PointedActionIso (pointedTrivialTorsor G) X.
Proof.
  revert X; intros [X x]. exists (triviality_isomorphism X x).
  simpl. apply univ_function_pointed.
Defined.

Definition Pointedtorsor_univalence {G:gr} {X Y:PointedTorsor G} :
  (X = Y) ≃ (PointedActionIso X Y).
Proof.
  intros.
  simple refine (weqcomp (total2_paths_equiv _ X Y) _).
  simple refine (weqbandf _ _ _ _).
  { intros.
    exact (weqcomp (weqonpathsincl underlyingAction underlyingAction_incl X Y)
                   Action_univalence). }
  destruct X as [X x], Y as [Y y]; simpl. intro p. destruct p; simpl.
  exact (idweq _).
Defined.

Definition ClassifyingSpace G := pointedType (Torsor G) (trivialTorsor G).
Definition E := PointedTorsor.
Definition B := ClassifyingSpace.
Definition π {G:gr} := underlyingTorsor : E G -> B G.

Lemma isBaseConnected_BG (G:gr) : isBaseConnected (B G).
Proof.
  intros X. use (hinhfun _ (torsor_nonempty X)); intros x.
  exact (torsor_eqweq_to_path (triviality_isomorphism X x)).
Defined.

Goal ∏ (G:gr), triviality_isomorphism (trivialTorsor G) (unel G) = idActionIso (trivialTorsor G).
  Fail reflexivity.
Abort.

Goal ∏ (G:gr), isBaseConnected_BG G (trivialTorsor G) = hinhpr (idpath (trivialTorsor G)).
  intros.
  unfold isBaseConnected_BG, pr2.
  change (pr1 (trivialTorsor G) : Type) with (G : Type).
  change (torsor_nonempty (trivialTorsor G)) with (hinhpr (unel G)).
  change (hinhpr (torsor_eqweq_to_path (triviality_isomorphism (trivialTorsor G) (unel G)))
          = hinhpr (idpath (trivialTorsor G))).
  apply maponpaths.
  Fail reflexivity.
Abort.

Lemma isConnected_BG (G:gr) : isConnected (B G).
Proof.
  apply baseConnectedness. apply isBaseConnected_BG.
Defined.

Lemma iscontr_EG (G:gr) : iscontr (E G).
Proof.
  intros. exists (pointedTrivialTorsor G). intros [X x].
  apply pathsinv0. apply (invweq Pointedtorsor_univalence).
  apply pointed_triviality_isomorphism.
Defined.

Theorem loopsBG (G:gr) : G ≃ Ω (B G).
Proof.
  intros.
  simple refine (weqcomp _ (invweq torsor_univalence)).
  apply trivialTorsorRightMultiplication.
Defined.

Definition loopsBG_comp (G:gr) (g:G) :
  loopsBG G g = invmap torsor_univalence (trivialTorsorAuto G g).
Proof.
  reflexivity.
Defined.

Definition loopsBG_comp' {G:gr} (p : Ω (B G)) :
  invmap (loopsBG G) p = path_to_ActionIso (maponpaths underlyingAction p) (unel G).
Proof.
  reflexivity.
Defined.

Definition loopsBG_comp_2 (G:gr) (g h:G)
  : castTorsor (loopsBG G g) h = (h*g)%multmonoid.
Proof.
  exact (torsor_univalence_inv_comp_eval (trivialTorsorAuto G g) h).
Defined.

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
compile-command: "make -C ../.. UniMath/CategoryTheory/RepresentableFunctors/GroupAction.vo"
End:
*)
