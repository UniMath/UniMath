(****************************************************
  Benedikt Ahrens and Anders Mörtberg, October 2015
*****************************************************)

(** *************************************************

Contents :

	    Definition of limits

*****************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section move_upstream.

Lemma path_to_ctr (A : UU) (B : A -> UU) (isc : iscontr (total2 (fun a => B a)))
           (a : A) (p : B a) : a = pr1 (pr1 isc).
Proof.
exact (maponpaths pr1 (pr2 isc (tpair _ a p))).
Defined.

Lemma uniqueExists (A : UU) (P : A -> UU)
  (Hexists : iscontr (total2 (fun a => P a)))
  (a b : A) (Ha : P a) (Hb : P b) : a = b.
Proof.
assert (H : tpair _ _ Ha = tpair _ _ Hb).
  now apply proofirrelevance, isapropifcontr.
exact (base_paths _ _ H).
Defined.

End move_upstream.

Section lim_def.

(* A cone with tip c over a diagram d *)
(*
Definition cocone {g : graph} (d : diagram g C) (c : C) : UU :=
  Σ (f : ∀ (v : vertex g), C⟦dob d v,c⟧),
    ∀ (u v : vertex g) (e : edge u v), dmor d e ;; f v = f u.
*)

(* Definition opp_diagram g C := diagram g C^op. *)

Definition cone {J C : precategory} (F : functor J C) (c : C) : UU :=
  Σ (f : ∀ (v : J), C⟦c,F v⟧),
    ∀ (u v : J) (e : J⟦u,v⟧), f u ;; # F e = f v.

(*
Definition mk_cocone {g : graph} {d : diagram g C} {c : C}
  (f : ∀ v, C⟦dob d v,c⟧) (Hf : ∀ u v e, dmor d e ;; f v = f u) :
  cocone d c := tpair _ f Hf.
*)

Definition mk_cone {J C : precategory} {F : functor J C} {c : C}
  (f : ∀ v, C⟦c, F v⟧) (Hf : ∀ u v (e : J⟦u,v⟧) , f u ;; # F e  = f v) :
  cone F c := tpair _ f Hf.

Definition coneOut {J C : precategory} {F : functor J C} {c : C} (cc : cone F c) :
  ∀ v, C⟦c, F v⟧ := pr1 cc.

Lemma coneOutCommutes {J C : precategory} {F : functor J C} {c : C}
  (cc : cone F c) : ∀ u v (e : J⟦u,v⟧), coneOut cc u ;; # F e = coneOut cc v.
Proof.
apply (pr2 cc).
Qed.

Definition isLimCone {J C : precategory} (F : functor J C)
  (l : C) (cc0 : cone F l) : UU := ∀ (c : C) (cc : cone F c),
    iscontr (Σ x : C⟦c,l⟧, ∀ v, x ;; coneOut cc0 v = coneOut cc v).

Definition LimCone {J C : precategory} (F : functor J C) : UU :=
  Σ (A : (Σ l, cone F l)), isLimCone F (pr1 A) (pr2 A).

Definition mk_LimCone {J C : precategory} (F : functor J C)
  (c : C) (cc : cone F c) (isCC : isLimCone F c cc) : LimCone F :=
  tpair _ (tpair _ c cc) isCC.

Definition Lims : UU := ∀ {J C : precategory} (F : functor J C), LimCone F.
Definition hasLims : UU  :=
  ∀ {J C : precategory} (F : functor J C), ishinh (LimCone F).

(* lim is the tip of the lim cone *)
Definition lim {J C : precategory} {F : functor J C} (CC : LimCone F) : C
  := pr1 (pr1 CC).

Definition limCone {J C : precategory} {F : functor J C} (CC : LimCone F) :
  cone F (lim CC) := pr2 (pr1 CC).

Definition limOut {J C : precategory} {F : functor J C} (CC : LimCone F) :
  ∀ v, C⟦lim CC,F v⟧ := coneOut (limCone CC).

Lemma limOutCommutes {J C : precategory} {F : functor J C}
  (CC : LimCone F) : ∀ u v (e : J⟦u,v⟧),
   limOut CC u ;; # F e = limOut CC v.
Proof.
exact (coneOutCommutes (limCone CC)).
Qed.

Lemma limUnivProp {J C : precategory} {F : functor J C}
  (CC : LimCone F) : ∀ (c : C) (cc : cone F c),
  iscontr (Σ x : C⟦c, lim CC⟧, ∀v, x ;; limOut CC v = coneOut cc v).
Proof.
exact (pr2 CC).
Qed.

Lemma isaprop_isLimCone {J C : precategory} (F : functor J C) (c0 : C)
  (cc0 : cone F c0) : isaprop (isLimCone F c0 cc0).
Proof.
repeat (apply impred; intro).
apply isapropiscontr.
Qed.

Definition isLimCone_LimCone {J C : precategory} {F : functor J C}
  (CC : LimCone F)
  : isLimCone F (lim CC) (tpair _ (limOut CC) (limOutCommutes CC))
  := pr2 CC.

Definition limArrow {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (cc : cone F c) : C⟦c, lim CC⟧ := pr1 (pr1 (isLimCone_LimCone CC c cc)).

Lemma limArrowCommutes {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (cc : cone F c) u :
   limArrow CC c cc ;; limOut CC u = coneOut cc u.
Proof.
exact ((pr2 (pr1 (isLimCone_LimCone CC _ cc))) u).
Qed.

Lemma limArrowUnique {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (cc : cone F c) (k : C⟦c, lim CC⟧)
  (Hk : ∀ u, k ;; limOut CC u = coneOut cc u) :
  k = limArrow CC c cc.
Proof.
now apply path_to_ctr, Hk.
Qed.

Lemma Cone_precompose {J C : precategory} {F : functor J C}
  {c : C} (cc : cone F c) (x : C) (f : C⟦x,c⟧) :
    ∀ u v (e : J⟦u,v⟧), (f ;; coneOut cc u) ;; # F e = f ;; coneOut cc v.
Proof.
now intros u v e; rewrite <- assoc, coneOutCommutes.
Qed.

Lemma limArrowEta {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (f : C⟦c, lim CC⟧) :
  f = limArrow CC c (tpair _ (λ u, f ;; limOut CC u)
                 (Cone_precompose (limCone CC) c f)).
Proof.
now apply limArrowUnique.
Qed.

Definition limOfArrows {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∀ u, C⟦F1 u,F2 u⟧)
  (fNat : ∀ u v (e : J⟦u,v⟧), f u ;; # F2 e = # F1 e ;; f v) :
  C⟦lim CC1 , lim CC2⟧.
Proof.
apply limArrow; simple refine (mk_cone _ _).
- now intro u; apply (limOut CC1 u ;; f u).
- abstract (intros u v e; simpl;
            now rewrite <- assoc, fNat, assoc, limOutCommutes).
Defined.

Lemma limOfArrowsOut {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∀ u, C⟦F1 u,F2 u⟧)
  (fNat : ∀ u v (e : J⟦u,v⟧), f u ;; # F2 e = # F1 e ;; f v) :
    ∀ u, limOfArrows CC1 CC2 f fNat ;; limOut CC2 u =
          limOut CC1 u ;; f u.
Proof.
now unfold limOfArrows; intro u; rewrite limArrowCommutes.
Qed.

Lemma postCompWithLimOfArrows_subproof
  {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∀ u, C⟦F1 u,F2 u⟧)
  (fNat : ∀ u v (e : J⟦u,v⟧), f u ;; # F2 e = # F1 e ;; f v)
  (x : C) (cc : cone F1 x) u v (e : J⟦u,v⟧) :
    (coneOut cc u ;; f u) ;; # F2 e = coneOut cc v ;; f v.
Proof.
now rewrite <- (coneOutCommutes cc u v e), <- assoc, fNat, assoc.
Defined.

Lemma postcompWithLimOfArrows
  {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∀ u, C⟦F1 u,F2 u⟧)
  (fNat : ∀ u v (e : J⟦u,v⟧), f u ;; # F2 e = # F1 e ;; f v)
  (x : C) (cc : cone F1 x) :
     limArrow CC1 x cc ;; limOfArrows CC1 CC2 f fNat =
       limArrow CC2 x (mk_cone (λ u, coneOut cc u ;; f u)
         (postCompWithLimOfArrows_subproof CC1 CC2 f fNat x cc)).
Proof.
apply limArrowUnique; intro u.
now rewrite <- assoc, limOfArrowsOut, assoc, limArrowCommutes.
Qed.

Lemma precompWithLimArrow {J C : precategory} {F : functor J C}
 (CC : LimCone F) (c : C) (cc : cone F c) (d : C) (k : C⟦d,c⟧) :
   k ;; limArrow CC c cc  =
   limArrow CC d (mk_cone (λ u, k ;; coneOut cc u)
              (Cone_precompose cc d k)).
Proof.
apply limArrowUnique.
now intro u; rewrite <- assoc, limArrowCommutes.
Qed.

Lemma lim_endo_is_identity {J C : precategory} {F : functor J C}
  (CC : LimCone F) (k : lim CC ⇒ lim CC)
  (H : ∀ u, k ;; limOut CC u = limOut CC u) :
  identity _ = k.
Proof.
unshelve refine (uniqueExists _ _ (limUnivProp CC _ _) _ _ _ _).
- now apply (limCone CC).
- now intros v; apply id_left.
- now apply H.
Qed.

(*
Definition Cocone_by_postcompose {g : graph} (D : diagram g C)
 (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) : cocone D d.
Proof.
now exists (λ u, coconeIn cc u ;; k); apply Cocone_postcompose.
Defined.

Lemma isColim_weq_subproof1 {g : graph} (D : diagram g C)
  (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) :
  ∀ u, coconeIn cc u ;; k = pr1 (Cocone_by_postcompose D c cc d k) u.
Proof.
now intro u.
Qed.

Lemma isColim_weq_subproof2 (g : graph) (D : diagram g C)
  (c : C) (cc : cocone D c) (H : ∀ d, isweq (Cocone_by_postcompose D c cc d))
  (d : C) (cd : cocone D d) (u : vertex g) :
    coconeIn cc u ;; invmap (weqpair _ (H d)) cd = coconeIn cd u.
Proof.
rewrite (isColim_weq_subproof1 D c cc d (invmap (weqpair _ (H d)) _) u).
set (p := homotweqinvweq (weqpair _ (H d)) cd); simpl in p.
now rewrite p.
Qed.

Lemma isColim_weq {g : graph} (D : diagram g C) (c : C) (cc : cocone D c) :
  isColimCocone D c cc <-> ∀ d, isweq (Cocone_by_postcompose D c cc d).
Proof.
split.
- intros H d.
  refine (gradth _ _ _ _).
  + intros k.
    exact (colimArrow (mk_ColimCocone D c cc H) _ k).
  + abstract (intro k; simpl;
              now apply pathsinv0, (colimArrowEta (mk_ColimCocone D c cc H))).
  + abstract (simpl; intro k;
              apply total2_paths_second_isaprop;
                [ now repeat (apply impred; intro); apply hsC
                | destruct k as [k Hk]; simpl; apply funextsec; intro u;
                  now apply (colimArrowCommutes (mk_ColimCocone D c cc H))]).
- intros H d cd.
  refine (tpair _ _ _).
  + exists (invmap (weqpair _ (H d)) cd).
    abstract (intro u; now apply isColim_weq_subproof2).
  + abstract (intro t; apply total2_paths_second_isaprop;
                [ now apply impred; intro; apply hsC
                | destruct t as [t Ht]; simpl;
                  apply (invmaponpathsweq (weqpair _ (H d))); simpl;
                  apply total2_paths_second_isaprop;
                    [ now repeat (apply impred; intro); apply hsC
                    | simpl; apply pathsinv0, funextsec; intro u; rewrite Ht;
                      now apply isColim_weq_subproof2]]).
Defined.
*)
End lim_def.

Arguments Lims : clear implicits.

Section LimFunctor.

Variable A C : precategory.
Variable hsC : has_homsets C.
Variable (J : precategory).
Variable (D : functor J [A, C, hsC]).

Definition functor_pointwise (a : A) : functor J C.
Proof.
mkpair.
- apply (tpair _ (fun v => pr1 (D v) a)).
  intros u v e; simpl; apply (pr1 (# D e) a).
- abstract (mkpair;
    [ intro x; simpl;
      apply (toforallpaths _ _ _ (maponpaths pr1 (functor_id D x)) a)
    | intros x y z f g; simpl;
      apply (toforallpaths _ _ _ (maponpaths pr1 (functor_comp D x y z f g)) a)]).
Defined.

Variable (HCg : forall (a : A), LimCone (functor_pointwise a)).

Definition LimFunctor_ob (a : A) : C := lim (HCg a).

Definition LimFunctor_mor (a a' : A) (f : A⟦a, a'⟧) :
  C⟦LimFunctor_ob a,LimFunctor_ob a'⟧.
Proof.
simple refine (limOfArrows _ _ _ _).
- now intro u; apply (# (pr1 (D u)) f).
- abstract (now intros u v e; simpl; apply (nat_trans_ax (# D e))).
Defined.

Definition LimFunctor_data : functor_data A C := tpair _ _ LimFunctor_mor.

Lemma is_functor_LimFunctor_data : is_functor LimFunctor_data.
Proof.
split.
- intro a; simpl.
  apply pathsinv0, lim_endo_is_identity; intro u.
  unfold LimFunctor_mor; rewrite limOfArrowsOut.
  assert (H : # (pr1 (D u)) (identity a) = identity (pr1 (D u) a)).
    apply (functor_id (D u) a).
  now rewrite H, id_right.
- intros a b c fab fbc; simpl; unfold LimFunctor_mor.
  apply pathsinv0.
  eapply pathscomp0; [now apply postcompWithLimOfArrows|].
  apply pathsinv0, limArrowUnique; intro u.
  rewrite limOfArrowsOut, (functor_comp (D u)); simpl.
  now rewrite <- assoc.
Qed.

Definition LimFunctor : functor A C := tpair _ _ is_functor_LimFunctor_data.

Definition lim_nat_trans_in_data v : [A, C, hsC] ⟦ LimFunctor, D v ⟧.
Proof.
mkpair.
- intro a; exact (limOut (HCg a) v).
- abstract (intros a a' f; apply (limOfArrowsOut (HCg a) (HCg a'))).
Defined.

Definition cone_pointwise (F : [A,C,hsC]) (cc : cone D F) a :
  cone (functor_pointwise a) (pr1 F a).
Proof.
simple refine (mk_cone _ _).
- now intro v; apply (pr1 (coneOut cc v) a).
- abstract (intros u v e;
    now apply (nat_trans_eq_pointwise (coneOutCommutes cc u v e))).
Defined.

Lemma LimFunctor_unique (F : [A, C, hsC]) (cc : cone D F) :
  iscontr (Σ x : [A, C, hsC] ⟦ F, LimFunctor ⟧,
            ∀ v, x ;; lim_nat_trans_in_data v = coneOut cc v).
Proof.
admit.
(* mkpair. *)
(* - simple refine (tpair _ _ _). *)
(*   + apply (tpair _ (fun a => colimArrow (HCg a) _ (cocone_pointwise F cc a))). *)
(*     abstract (intros a a' f; simpl; *)
(*               eapply pathscomp0; *)
(*                 [ now apply precompWithColimOfArrows *)
(*                 | apply pathsinv0; eapply pathscomp0; *)
(*                   [ now apply postcompWithColimArrow *)
(*                   | apply colimArrowUnique; intro u; *)
(*                     eapply pathscomp0; *)
(*                       [ now apply colimArrowCommutes *)
(*                       | apply pathsinv0; now refine (nat_trans_ax _ _ _ _) ]]]). *)
(*   + abstract (intro u; apply (nat_trans_eq hsC); simpl; intro a; *)
(*               now apply (colimArrowCommutes (HCg a))). *)
(* - abstract (intro t; destruct t as [t1 t2]; *)
(*             apply subtypeEquality; simpl; *)
(*               [ intro; apply impred; intro u; apply functor_category_has_homsets *)
(*               | apply (nat_trans_eq hsC); simpl; intro a; *)
(*                 apply colimArrowUnique; intro u; *)
(*                 now apply (nat_trans_eq_pointwise (t2 u))]). *)
Admitted.

Lemma LimFunctorCone : LimCone D.
Proof.
simple refine (mk_LimCone _ _ _ _).
- exact LimFunctor.
- simple refine (mk_cone _ _).
  + now apply lim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq hsC);
                  intro a; apply (limOutCommutes (HCg a))).
- now intros F cc; simpl; apply (LimFunctor_unique _ cc).
Defined.

End LimFunctor.

(* Lemma LimsFunctorCategory (A C : precategory) (hsC : has_homsets C) *)
(*   (HC : Lims C) : Lims [A,C,hsC]. *)
(* Proof. *)
(* now intros g d; apply LimFunctorCone. *)
(* Defined. *)


(* (* TODO: move to opp_precat *) *)

(* Definition get_diagram (A C : precategory) (hsC : has_homsets C) *)
(*   (g : graph) (D : diagram g [A, C, hsC]^op) : *)
(*     diagram g [A^op, C^op, has_homsets_opp hsC]. *)
(* Proof. *)
(* apply (tpair _ (fun u => from_opp_to_opp_opp _ _ _ (pr1 D u))). *)
(* intros u v e; simpl. *)
(* simple refine (tpair _ _ _); simpl. *)
(*   + apply (pr2 D _ _ e). *)
(*   + abstract (intros a b f; apply pathsinv0, (pr2 (pr2 D u v e) b a f)). *)
(* Defined. *)

(* Definition get_cocone  (A C : precategory) (hsC : has_homsets C) *)
(*   (g : graph) (D : diagram g [A, C, hsC]^op) (F : functor A C) (ccF : cocone D F) : *)
(*   cocone (get_diagram A C hsC g D) (functor_opp F). *)
(* Proof. *)
(* destruct ccF as [t p]. (* If I remove this destruct the Qed for LimsFunctorCategory *) *)
(* (*                  takes twice as long *) *)
(* simple refine (mk_cocone _ _). *)
(* - intro u; apply (tpair _ (pr1 (t u))). *)
(*   abstract (intros a b f; apply pathsinv0, (pr2 (t u) b a f)). *)
(* - abstract (intros u v e; apply (nat_trans_eq (has_homsets_opp hsC)); *)
(*             now intro a; simpl; rewrite <- (p u v e)). *)
(* Defined. *)

(* Lemma LimFunctorCone (A C : precategory) (hsC : has_homsets C) *)
(*   (g : graph) *)
(*   (D : diagram g [A, C, hsC]^op) *)
(*   (HC : ∀ a : A^op, *)
(*             LimCone *)
(*               (diagram_pointwise A^op C^op (has_homsets_opp hsC) g *)
(*                  (get_diagram A C hsC g D) a)) *)

(*   : LimCone D. *)
(* Proof. *)
(* set (HColim := ColimFunctorCocone A^op C^op  (has_homsets_opp hsC) g (get_diagram _ _ _ _ D) HC). *)
(* destruct HColim as [pr1x pr2x]. *)
(* destruct pr1x as [pr1pr1x pr2pr1x]. *)
(* destruct pr2pr1x as [pr1pr2pr1x pr2pr2pr1x]. *)
(* simpl in *. *)
(* use (mk_ColimCocone _ (from_opp_opp_to_opp _ _ _ pr1pr1x)). *)
(* - simple refine (mk_cocone _ _). *)
(*   + simpl; intros. *)
(*     simple refine (tpair _ _ _). *)
(*     * intro a; apply (pr1pr2pr1x v a). *)
(*     * abstract (intros a b f; apply pathsinv0, (nat_trans_ax (pr1pr2pr1x v) (*b a f*))). *)
(*   + abstract (intros u v e; apply (nat_trans_eq hsC); simpl; intro a; *)
(*               now rewrite <- (pr2pr2pr1x u v e)). *)
(* - intros F ccF. *)
(*   set (H := pr2x (from_opp_to_opp_opp _ _ _ F) (get_cocone _ _ _ _ _ _ ccF)). *)
(*   destruct H as [H1 H2]. *)
(*   destruct H1 as [α Hα]. *)
(*   simpl in *. *)
(*   simple refine (tpair _ _ _). *)
(*   + simple refine (tpair _ _ _). *)
(*     * exists α. *)
(*       abstract (intros a b f; simpl; now apply pathsinv0, (nat_trans_ax α b a f)). *)
(*     * abstract (intro u; apply (nat_trans_eq hsC); intro a; *)
(*         destruct ccF as [t p]; apply (toforallpaths _ _ _ (maponpaths pr1 (Hα u)) a)). *)
(*   + intro H; destruct H as [f Hf]; apply subtypeEquality. *)
(*     * abstract (intro β; repeat (apply impred; intro); *)
(*         now apply (has_homsets_opp (functor_category_has_homsets A C hsC))). *)
(*     * match goal with |[ H2 : ∀ _ : ?TT ,  _ = _ ,,_   |- _ ] => *)
(*                        transparent assert (T : TT) end. *)
(*       (* *) *)
(* (*       refine (let T : Σ x : nat_trans pr1pr1x (functor_opp F), *) *)
(* (*                          ∀ v, nat_trans_comp (functor_opp (pr1 D v)) _ _ *) *)
(* (*                                 (pr1pr2pr1x v) x = *) *)
(* (*                                coconeIn (get_cocone A C hsC g D F ccF) v := *) *)
(* (*                   _ in _). *) *)
(* (*       *) *)
(*       { simple refine (tpair _ (tpair _ (pr1 f) _) _); simpl. *)
(*         - abstract (intros x y fxy; apply pathsinv0, (pr2 f y x fxy)). *)
(*         - abstract (intro u; apply (nat_trans_eq (has_homsets_opp hsC)); intro x; *)
(*             destruct ccF as [t p]; apply (toforallpaths _ _ _ (maponpaths pr1 (Hf u)) x)). *)
(*       } *)
(*       set (T' := maponpaths pr1 (H2 T)); simpl in T'. *)
(*       apply (nat_trans_eq hsC); intro a; simpl. *)
(*       now rewrite <- T'. *)
(* Defined. *)

(* Lemma LimsFunctorCategory (A C : precategory) (hsC : has_homsets C) *)
(*   (HC : Lims C) : Lims [A,C,hsC]. *)
(* Proof. *)
(* intros g D. *)
(* apply LimFunctorCone. *)
(* intros. *)
(* apply HC. *)
(* Defined. *)

(* End LimFunctor. *)

(*

(* Defines colimits in functor categories when the target has colimits *)
Section ColimFunctor.

Variable A C : precategory.
Variable HC : Colims C.
Variable hsC : has_homsets C.
Variable g : graph.
Variable D : diagram g [A, C, hsC].

Definition diagram_pointwise (a : A) : diagram g C.
Proof.
exists (fun v => pr1 (dob D v) a); intros u v e.
now apply (pr1 (dmor D e) a).
Defined.

Let HCg a := HC g (diagram_pointwise a).

Definition ColimFunctor_ob (a : A) : C := colim (HCg a).

Definition ColimFunctor_mor (a a' : A) (f : A⟦a, a'⟧) :
  C⟦ColimFunctor_ob a,ColimFunctor_ob a'⟧.
Proof.
refine (colimOfArrows _ _ _ _).
- now intro u; apply (# (pr1 (dob D u)) f).
- abstract (now intros u v e; simpl; apply pathsinv0, (nat_trans_ax (dmor D e))).
Defined.

Definition ColimFunctor_data : functor_data A C := tpair _ _ ColimFunctor_mor.

Lemma is_functor_ColimFunctor_data : is_functor ColimFunctor_data.
Proof.
split.
- intro a; simpl.
  apply pathsinv0, colim_endo_is_identity; intro u.
  unfold ColimFunctor_mor.
  now rewrite colimOfArrowsIn, (functor_id (dob D u)), id_left.
- intros a b c fab fbc; simpl; unfold ColimFunctor_mor.
  apply pathsinv0.
  eapply pathscomp0; [now apply precompWithColimOfArrows|].
  apply pathsinv0, colimArrowUnique; intro u.
  rewrite colimOfArrowsIn.
  rewrite (functor_comp (dob D u)).
  now apply pathsinv0, assoc.
Qed.

Definition ColimFunctor : functor A C := tpair _ _ is_functor_ColimFunctor_data.

Definition colim_nat_trans_in_data v : [A, C, hsC] ⟦ dob D v, ColimFunctor ⟧.
Proof.
refine (tpair _ _ _).
- intro a; exact (colimIn (HCg a) v).
- abstract (intros a a' f;
            now apply pathsinv0, (colimOfArrowsIn _ _ (HCg a) (HCg a'))).
Defined.

Definition cocone_pointwise (F : [A,C,hsC]) (cc : cocone D F) a :
  cocone (diagram_pointwise a) (pr1 F a).
Proof.
refine (mk_cocone _ _).
- now intro v; apply (pr1 (coconeIn cc v) a).
- abstract (intros u v e;
    now apply (nat_trans_eq_pointwise  (coconeInCommutes cc u v e))).
Defined.

Lemma ColimFunctor_unique (F : [A, C, hsC]) (cc : cocone D F) :
  iscontr (Σ x : [A, C, hsC] ⟦ ColimFunctor, F ⟧,
            ∀ v : vertex g, colim_nat_trans_in_data v ;; x = coconeIn cc v).
Proof.
refine (tpair _ _ _).
- refine (tpair _ _ _).
  + apply (tpair _ (fun a => colimArrow (HCg a) _ (cocone_pointwise F cc a))).
    abstract (intros a a' f; simpl;
              eapply pathscomp0;
                [ now apply precompWithColimOfArrows
                | apply pathsinv0; eapply pathscomp0;
                  [ now apply postcompWithColimArrow
                  | apply colimArrowUnique; intro u;
                    eapply pathscomp0;
                      [ now apply colimArrowCommutes
                      | now apply pathsinv0, nat_trans_ax ]]]).
  + abstract (intro u; apply (nat_trans_eq hsC); simpl; intro a;
              now apply (colimArrowCommutes (HCg a))).
- abstract (intro t; destruct t as [t1 t2];
            apply (total2_paths_second_isaprop); simpl;
              [ apply impred; intro u; apply functor_category_has_homsets
              | apply (nat_trans_eq hsC); simpl; intro a;
                apply colimArrowUnique; intro u;
                now apply (nat_trans_eq_pointwise (t2 u))]).
Defined.

Lemma ColimFunctorCocone : ColimCocone D.
Proof.
refine (mk_ColimCocone _ _ _ _).
- exact ColimFunctor.
- refine (mk_cocone _ _).
  + now apply colim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq hsC);
                  intro a; apply (colimInCommutes (HCg a))).
- now intros F cc; simpl; apply (ColimFunctor_unique _ cc).
Defined.

End ColimFunctor.

Lemma ColimsFunctorCategory (A C : precategory) (hsC : has_homsets C)
  (HC : Colims C) : Colims [A,C,hsC].
Proof.
now intros g d; apply ColimFunctorCocone.
Defined.
*)