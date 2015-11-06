(****************************************************
  Benedikt Ahrens and Anders Mörtberg, October 2015
*****************************************************)

(** *************************************************

Contents :

	    Definition of limits

*****************************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.colimits.colimits.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Section lim_def.

Context {C : precategory} (hsC : has_homsets C).

(* A cone with tip c over a diagram d *)
(*
Definition cocone {g : graph} (d : diagram g C) (c : C) : UU :=
  Σ (f : ∀ (v : vertex g), C⟦dob d v,c⟧),
    ∀ (u v : vertex g) (e : edge u v), dmor d e ;; f v = f u.
*)

Definition opp_diagram g C := diagram g C^op.

Definition cone {g : graph} (d : diagram g C^op) (c : C) : UU :=
  @cocone C^op g d c.

(*
Definition mk_cocone {g : graph} {d : diagram g C} {c : C}
  (f : ∀ v, C⟦dob d v,c⟧) (Hf : ∀ u v e, dmor d e ;; f v = f u) :
  cocone d c := tpair _ f Hf.
*)

Definition mk_cone {g : graph} {d : diagram g C^op} {c : C}
  (f : ∀ v, C⟦c, dob d v⟧) (Hf : ∀ u v (e : edge u v) , f v ;; dmor d e  = f u) :
  cone d c
  := tpair _ f Hf.

(* The injections to c in the cocone *)
Definition coneOut {g : graph} {d : diagram g C^op} {c : C} (cc : cone d c) :
  ∀ v, C⟦c, dob d v⟧ := coconeIn cc.

Lemma coneOutCommutes {g : graph} {d : diagram g C^op} {c : C} (cc : cone d c) :
  ∀ u v (e : edge u v), coneOut cc v ;; dmor d e = coneOut cc u.
Proof.
  apply (coconeInCommutes cc).
Qed.

(* cc0 is a colimit cocone if for any other cocone cc over the same
   diagram there is a unique morphism from the tip of cc0 to the tip
   of cc *)
Definition isLimCone {g : graph} (d : diagram g C^op) (c0 : C)
  (cc0 : cone d c0) : UU :=
   isColimCocone _ _ cc0.
(*
∀ (c : C) (cc : cone d c),
      isColimCocone
    iscontr (Σ x : C⟦c0,c⟧, ∀ v, coconeIn cc0 v ;; x = coconeIn cc v).
*)

Definition LimCone {g : graph} (d : diagram g C^op) : UU :=
  ColimCocone d.

Definition mk_LimCone {g : graph} (d : diagram g C^op)
  (c : C) (cc : cone d c) (isCC : isLimCone d c cc) : LimCone d.
Proof.
refine (mk_ColimCocone _ _ _ _  ).
- apply c.
- apply cc.
- apply isCC.
Defined.

Definition Lims : UU := ∀ {g : graph} (d : diagram g C^op), LimCone d.
Definition hasLims : UU  :=
  ∀ {g : graph} (d : diagram g C^op), ishinh (LimCone d).

(* lim is the tip of the lim cone *)
Definition lim {g : graph} {d : diagram g C^op} (CC : LimCone d) : C
  := colim CC.

Definition limCone {g : graph} {d : diagram g C^op} (CC : LimCone d) :
  cone d (lim CC) := colimCocone CC.

Definition limOut {g : graph} {d : diagram g C^op} (CC : LimCone d) :
  ∀ (v : vertex g), C⟦lim CC, dob d v⟧ := coneOut (limCone CC).

Lemma limOutCommutes {g : graph} {d : diagram g C^op}
  (CC : LimCone d) : ∀ (u v : vertex g) (e : edge u v),
   limOut CC v ;; dmor d e = limOut CC u.
Proof.
exact (coneOutCommutes (limCone CC)).
Qed.

Lemma limUnivProp {g : graph} {d : diagram g C^op}
  (CC : LimCone d) : ∀ (c : C) (cc : cone d c),
  iscontr (Σ x : C⟦c, lim CC⟧, ∀ (v : vertex g), x ;; limOut CC v = coneOut cc v).
Proof.
apply (colimUnivProp CC).
Qed.

Definition isLimCone_LimCone {g : graph} {d : diagram g C^op}
    (CC : LimCone d)
  : isLimCone d (lim CC) (tpair _ (limOut CC) (limOutCommutes CC))
  := isColimCocone_ColimCocone CC.

Definition limArrow {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (cc : cone d c) : C⟦c, lim CC⟧.
Proof.
 exact (colimArrow CC _ cc).
Defined.

Lemma limArrowCommutes {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (cc : cone d c) (u : vertex g) :
   limArrow CC c cc ;; limOut CC u = coneOut cc u.
Proof.
  exact (colimArrowCommutes CC _ cc _ ).
Qed.

Lemma limArrowUnique {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (cc : cone d c) (k : C⟦c, lim CC⟧)
  (Hk : ∀ (u : vertex g), k ;; limOut CC u = coneOut cc u) :
  k = limArrow CC c cc.
Proof.
  apply (colimArrowUnique CC c cc k Hk).
Qed.

Lemma Cone_precompose {g : graph} {d : diagram g C^op}
  {c : C} (cc : cone d c) (x : C) (f : C⟦x,c⟧) :
    ∀ u v (e : edge u v), (f ;; coneOut cc v) ;; dmor d e = f ;; coneOut cc u.
Proof.
  apply (Cocone_postcompose cc x f).
Qed.

Lemma limArrowEta {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (f : C⟦c, lim CC⟧) :
  f = limArrow CC c (tpair _ (λ u, f ;; limOut CC u)
                 (Cone_precompose (limCone CC) c f)).
Proof.
now apply limArrowUnique.
Qed.

Definition limOfArrows {g : graph} {d1 d2 : diagram g C^op}
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), f v ;; (dmor d2 e : C⟦dob d2 v, dob d2 u⟧)
                              =
                                (dmor d1 e : C⟦dob d1 v, dob d1 u⟧);; f u) :
  C⟦lim CC1 , lim CC2⟧.
Proof.
  refine (colimOfArrows CC2 CC1 _ _ ).
  - apply f.
  - apply fNat.
Defined.

Lemma limOfArrowsOut {g : graph} (d1 d2 : diagram g C^op)
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), f v ;; dmor d2 e = (dmor d1 e : C ⟦ _ , _ ⟧)  ;; f u) :
    ∀ u, limOfArrows CC1 CC2 f fNat ;; limOut CC2 u =
          limOut CC1 u ;; f u.
Proof.
  apply (colimOfArrowsIn _ _ CC2 CC1 f fNat).
Qed.

Lemma postCompWithLimOfArrows_subproof {g : graph} {d1 d2 : diagram g C^op}
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), f v ;; dmor d2 e = (dmor d1 e : C ⟦ _ , _ ⟧)  ;; f u)
  (x : C) (cc : cone d1 x) u v (e : edge u v) :
    (coneOut cc v ;; f v) ;; dmor d2 e = coneOut cc u ;; f u.
Proof.
  apply (preCompWithColimOfArrows_subproof CC2 CC1 f fNat x cc _ _ e).
Defined.

Lemma postcompWithColimOfArrows {g : graph} (d1 d2 : diagram g C^op)
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), f v ;; dmor d2 e = (dmor d1 e : C ⟦ _ , _ ⟧)  ;; f u)
  (x : C) (cc : cone d1 x) :
     limArrow CC1 x cc ;; limOfArrows CC1 CC2 f fNat =
       limArrow CC2 x (mk_cone (λ u, coneOut cc u ;; f u)
         (postCompWithLimOfArrows_subproof CC1 CC2 f fNat x cc)).
Proof.
  apply limArrowUnique.
  intro.
  rewrite <- assoc.
  rewrite limOfArrowsOut.
  rewrite assoc.
  rewrite limArrowCommutes.
  apply idpath.
Qed.

Lemma precompWithLimArrow {g : graph} (D : diagram g C^op)
 (CC : LimCone D) (c : C) (cc : cone D c) (d : C) (k : C⟦d,c⟧) :
   k ;; limArrow CC c cc  =
   limArrow CC d (mk_cone (λ u, k ;; coneOut cc u)
              (Cone_precompose cc d k)).
Proof.
  apply limArrowUnique.
  now intro u; rewrite <- assoc, limArrowCommutes.
Qed.

Lemma lim_endo_is_identity {g : graph} (D : diagram g C^op)
  (CC : LimCone D) (k : lim CC ⇒ lim CC)
  (H : ∀ u, k ;; limOut CC u = limOut CC u) :
  identity _ = k.
Proof.
refine (uniqueExists _ _ (limUnivProp CC _ _) _ _ _ _).
- now apply (limCone CC).
- intros v; simpl.
  unfold compose. simpl.
  now apply id_left.
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

(* TODO: move to opp_precat *)


Definition get_diagram (A C : precategory) (hsC : has_homsets C)
  (g : graph) (D : diagram g [A, C, hsC]^op) :
    diagram g [A^op, C^op, has_homsets_opp hsC].
Proof.
apply (tpair _ (fun u => from_opp_to_opp_opp _ _ _ (pr1 D u))).
intros u v e; simpl.
refine (tpair _ _ _); simpl.
  + apply (pr2 D _ _ e).
  + abstract (intros a b f; apply pathsinv0, (pr2 (pr2 D u v e) b a f)).
Defined.

Definition get_cocone  (A C : precategory) (hsC : has_homsets C)
  (g : graph) (D : diagram g [A, C, hsC]^op) (F : functor A C) (ccF : cocone D F) :
  cocone (get_diagram A C hsC g D) (functor_opp F).
Proof.
destruct ccF as [t p]. (* If I remove this destruct the Qed for LimsFunctorCategory
                 takes twice as long *)
refine (mk_cocone _ _).
- intro u; apply (tpair _ (pr1 (t u))).
  abstract (intros a b f; apply pathsinv0, (pr2 (t u) b a f)).
- abstract (intros u v e; apply (nat_trans_eq (has_homsets_opp hsC));
            now intro a; simpl; rewrite <- (p u v e)).
Defined.

Lemma LimFunctorCone (A C : precategory) (hsC : has_homsets C)
  (g : graph)
  (D : diagram g [A, C, hsC]^op)
  (HC : ∀ a : A^op,
            LimCone
              (diagram_pointwise A^op C^op (has_homsets_opp hsC) g
                 (get_diagram A C hsC g D) a))

  : LimCone D.
Proof.
set (HColim := ColimFunctorCocone A^op C^op  (has_homsets_opp hsC) g (get_diagram _ _ _ _ D) HC).
destruct HColim as [pr1x pr2x].
destruct pr1x as [pr1pr1x pr2pr1x].
destruct pr2pr1x as [pr1pr2pr1x pr2pr2pr1x].
simpl in *.
refine (mk_ColimCocone _ (from_opp_opp_to_opp _ _ _ pr1pr1x) _ _).
- refine (mk_cocone _ _).
  + simpl; intros.
    refine (tpair _ _ _).
    * intro a; apply (pr1pr2pr1x v a).
    * abstract (intros a b f; apply pathsinv0, (nat_trans_ax (pr1pr2pr1x v) (*b a f*))).
  + abstract (intros u v e; apply (nat_trans_eq hsC); simpl; intro a;
              now rewrite <- (pr2pr2pr1x u v e)).
- intros F ccF.
  set (H := pr2x (from_opp_to_opp_opp _ _ _ F) (get_cocone _ _ _ _ _ _ ccF)).
  destruct H as [H1 H2].
  destruct H1 as [α Hα].
  simpl in *.
  refine (tpair _ _ _).
  + refine (tpair _ _ _).
    * exists α.
      abstract (intros a b f; simpl; now apply pathsinv0, (nat_trans_ax α b a f)).
    * abstract (intro u; apply (nat_trans_eq hsC); intro a;
        destruct ccF as [t p]; apply (toforallpaths _ _ _ (maponpaths pr1 (Hα u)) a)).
  + intro H; destruct H as [f Hf]; apply subtypeEquality.
    * abstract (intro β; repeat (apply impred; intro);
        now apply (has_homsets_opp (functor_category_has_homsets A C hsC))).
    * match goal with |[ H2 : ∀ _ : ?TT ,  _ = _ ,,_   |- _ ] =>
                       refine (let T : TT := _ in _ ) end.
      (*
      refine (let T : Σ x : nat_trans pr1pr1x (functor_opp F),
                         ∀ v, nat_trans_comp (functor_opp (pr1 D v)) _ _
                                (pr1pr2pr1x v) x =
                               coconeIn (get_cocone A C hsC g D F ccF) v :=
                  _ in _).
      *)
      { refine (tpair _ (tpair _ (pr1 f) _) _); simpl.
        - abstract (intros x y fxy; apply pathsinv0, (pr2 f y x fxy)).
        - abstract (intro u; apply (nat_trans_eq (has_homsets_opp hsC)); intro x;
            destruct ccF as [t p]; apply (toforallpaths _ _ _ (maponpaths pr1 (Hf u)) x)).
      }
      set (T' := maponpaths pr1 (H2 T)); simpl in T'.
      apply (nat_trans_eq hsC); intro a; simpl.
      now rewrite <- T'.
Defined.

Lemma LimsFunctorCategory (A C : precategory) (hsC : has_homsets C)
  (HC : Lims C) : Lims [A,C,hsC].
Proof.
intros g D.
apply LimFunctorCone.
intros.
apply HC.
Defined.


End LimFunctor.

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