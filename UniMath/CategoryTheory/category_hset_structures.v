(** **********************************************************

Written by: Benedikt Ahrens, Anders Mörtberg

October 2015 - January 2016

************************************************************)


(** **********************************************************

Contents :
	    Colimits in HSET

	    Limits in HSET

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.limits.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

(* This should be moved upstream. Constructs the smallest eqrel
   containing a given relation *)
Section extras.

Variable A : UU.
Variable R0 : hrel A.

Lemma isaprop_eqrel_from_hrel a b :
  isaprop (∀ R : eqrel A, (∀ x y, R0 x y -> R x y) -> R a b).
Proof.
  apply impred; intro R; apply impred_prop.
Qed.

Definition eqrel_from_hrel : hrel A :=
  fun a b => hProppair _ (isaprop_eqrel_from_hrel a b).

Lemma iseqrel_eqrel_from_hrel : iseqrel eqrel_from_hrel.
Proof.
repeat split.
- intros x y z H1 H2 R HR.
  apply (eqreltrans R _ y); [ now apply H1 | now apply H2].
- now intros x R _; apply (eqrelrefl R).
- intros x y H R H'.
  now apply (eqrelsymm R), H.
Qed.

Lemma eqrel_impl a b : R0 a b -> eqrel_from_hrel a b.
Proof.
now intros H R HR; apply HR.
Qed.

(* eqrel_from_hrel is the *smallest* relation containing R0 *)
Lemma minimal_eqrel_from_hrel (R : eqrel A) (H : ∀ a b, R0 a b -> R a b) :
  ∀ a b, eqrel_from_hrel a b -> R a b.
Proof.
now intros a b H'; apply H'.
Qed.

End extras.

Arguments eqrel_from_hrel {_} _ _ _.


(** colimits in HSET *)
Section colimits.

Variable g : graph.
Variable D : diagram g HSET.

Local Definition cobase : UU := Σ j : vertex g, pr1hSet (dob D j).

(* Theory about hprop is in UniMath.Foundations.Basics.Propositions *)
Local Definition rel0 : hrel cobase := λ (ia jb : cobase),
  hProppair (ishinh (Σ f : edge (pr1 ia) (pr1 jb), dmor D f (pr2 ia) = pr2 jb))
            (isapropishinh _).

Local Definition rel : hrel cobase := eqrel_from_hrel rel0.

Lemma iseqrel_rel : iseqrel rel.
Proof.
now apply iseqrel_eqrel_from_hrel.
Qed.

Local Definition eqr : eqrel cobase := eqrelpair _ iseqrel_rel.

(* Defined in UniMath.Foundations.Basics.Sets *)
Definition colimHSET : HSET :=
  hSetpair (setquot eqr) (isasetsetquot _).

(*
           (X,~)
            | \
            |   \
            |     \
  setquotpr |       \
            |         \
            |           \
            |             \
            V              V
           X/~ ----------> (Y,=)
*)

Local Definition injections j : HSET ⟦dob D j, colimHSET⟧.
Proof.
intros Fj; apply (setquotpr _).
exact (tpair _ j Fj).
Defined.

(* Define the morphism out of the colimit *)
Section from_colim.

Variables (c : HSET) (cc : cocone D c).

Local Definition from_cobase : cobase -> pr1hSet c.
Proof.
now intro iA; apply (coconeIn cc (pr1 iA) (pr2 iA)).
Defined.

Local Definition from_cobase_rel : hrel cobase.
Proof.
intros x x'; exists (from_cobase x = from_cobase x').
now apply setproperty.
Defined.

Local Definition from_cobase_eqrel : eqrel cobase.
Proof.
exists from_cobase_rel.
repeat split.
- intros x y z H1 H2.
  exact (pathscomp0 H1 H2).
- intros x y H.
  exact (pathsinv0 H).
Defined.

Lemma rel0_impl a b (Hab : rel0 a b) : from_cobase_eqrel a b.
Proof.
apply Hab; clear Hab; intro H; simpl.
destruct H as [f Hf].
generalize (toforallpaths _ _ _ (coconeInCommutes cc (pr1 a) (pr1 b) f) (pr2 a)).
unfold compose, from_cobase; simpl; intro H.
now rewrite <- H, Hf.
Qed.

Lemma rel_impl a b (Hab : rel a b) : from_cobase_eqrel a b.
Proof.
now apply (@minimal_eqrel_from_hrel _ rel0); [apply rel0_impl|].
Qed.

Lemma iscomprel_from_base : iscomprelfun rel from_cobase.
Proof.
now intros a b; apply rel_impl.
Qed.

Definition from_colimHSET : HSET ⟦colimHSET, c⟧.
Proof.
now simpl; apply (setquotuniv _ _ from_cobase iscomprel_from_base).
Defined.

End from_colim.

Definition colimCoconeHSET : cocone D colimHSET.
Proof.
simple refine (mk_cocone _ _).
- now apply injections.
- abstract (intros u v e;
            apply funextfun; intros Fi; simpl;
            unfold compose, injections; simpl;
            apply (weqpathsinsetquot eqr), (eqrelsymm eqr), eqrel_impl, hinhpr; simpl;
            now exists e).
Defined.

Definition ColimHSETArrow (c : HSET) (cc : cocone D c) :
  Σ x : HSET ⟦ colimHSET, c ⟧, ∀ v : vertex g, injections v ;; x = coconeIn cc v.
Proof.
exists (from_colimHSET _ cc).
abstract (intro i; simpl; unfold injections, compose, from_colimHSET; simpl;
          apply funextfun; intro Fi; now rewrite (setquotunivcomm eqr)).
Defined.

Definition ColimCoconeHSET : ColimCocone D.
Proof.
apply (mk_ColimCocone _ colimHSET colimCoconeHSET); intros c cc.
exists (ColimHSETArrow _ cc).
abstract (intro f; apply subtypeEquality;
           [ intro; now apply impred; intro i; apply has_homsets_HSET
           | apply funextfun; intro x; simpl;
             apply (surjectionisepitosets (setquotpr eqr));
               [now apply issurjsetquotpr | now apply pr2 | ];
             intro y; destruct y as [u fu]; destruct f as [f Hf];
             now apply (toforallpaths _ _ _ (Hf u) fu)]).
Qed.

End colimits.

Lemma ColimsHSET : Colims HSET.
Proof.
now intros g d; apply ColimCoconeHSET.
Qed.

(* Direct construction of Coproducts in HSET *)
Lemma CoproductsHSET : Coproducts HSET.
Proof.
intros A B.
simple refine (mk_CoproductCocone _ _ _ _ _ _ _).
- simpl in *; apply (tpair _ (coprod A B)).
  abstract (apply isasetcoprod; apply setproperty).
- simpl in *; apply ii1.
- simpl in *; intros x; apply (ii2 x).
- apply (mk_isCoproductCocone _ has_homsets_HSET).
  intros C f g; simpl in *.
  simple refine (tpair _ _ _).
  * apply (tpair _ (sumofmaps f g)); split; apply idpath.
  * intros h; apply subtypeEquality.
    { abstract(intros x; apply isapropdirprod; apply has_homsets_HSET). }
    { abstract(destruct h as [t [ht1 ht2]]; simpl;
               apply funextfun; intro x;
               rewrite <- ht2, <- ht1; unfold compose; simpl;
               case x; intros; apply idpath). }
Defined.

Lemma CoproductsHSET_from_Colims : Coproducts HSET.
Proof.
exact (Coproducts_from_Colims _ has_homsets_HSET ColimsHSET).
Qed.

Lemma InitialHSET : Initial HSET.
Proof.
apply (mk_Initial emptyHSET).
apply mk_isInitial; intro a.
simple refine (tpair _ _ _).
- simpl; intro e; induction e.
- intro f; apply funextfun; intro e; induction e.
Defined.

Lemma InitialHSET_from_Colims : Initial HSET.
Proof.
now apply Initial_from_Colims, ColimsHSET.
Qed.

Section limits.

Variable g : graph.
Variable D : diagram g HSET^op.

Definition limset_UU : UU :=
  Σ (f : ∀ u : vertex g, pr1hSet (dob D u)),
    ∀ u v (e : edge u v), dmor D e (f v) = f u.

Definition limset : HSET.
Proof.
  exists limset_UU.
  abstract (apply (isofhleveltotal2 2);
            [ apply impred; intro; apply pr2 |
              intro f; repeat (apply impred; intro);
              apply isasetaprop;
              apply (pr2 (dob D t))]).
Defined.

Lemma LimConeHSET : LimCone D.
Proof.
  simple refine (mk_LimCone _ _ _ _ ).
  - apply limset.
  - simple refine (mk_cone _ _ ).
    + intro u. simpl.
      intro f.
      exact (pr1 f u).
    + intros u v e; simpl.
      apply funextfun.
      intro f; simpl.
      apply (pr2 f).
  - intros X CC.
    simple refine (tpair _ _ _ ).
    + simple refine (tpair _ _ _ ).
      * simpl.
        intro x.
        {
          simple refine (tpair _ _ _ ).
          - intro u.
            apply (coconeIn CC u x). (* TODO : hide implementation of limits *)
          - intros u v e. simpl.
            set (T := coconeInCommutes CC _ _ e).
            apply (toforallpaths _ _ _ T).
        }
      * intro v. apply idpath.
   + intro t.
     apply subtypeEquality.
     * intro; apply impred; intro.
       apply isaset_set_fun_space.
     * simpl.
       destruct t as [t p]; simpl.
       apply funextfun.
       intro x; simpl.
       unfold compose. simpl.
       {
         apply subtypeEquality.
         - intro; repeat (apply impred; intro).
           apply (setproperty (dob D t0)).
         - simpl.
           apply funextsec.
           intro u.
           simpl in p.
           set (p' := toforallpaths _ _ _ (p u)).
           apply p'.
       }
Qed.

End limits.

Lemma LimsHSET : Lims HSET.
Proof.
now intros g d; apply LimConeHSET.
Qed.

(* Direct construction of Products in HSET *)
Lemma ProductsHSET : Products HSET.
Proof.
intros A B.
simple refine (mk_ProductCone _ _ _ _ _ _ _).
- simpl in *; apply (tpair _ (dirprod A B)).
  abstract (apply isasetdirprod; apply setproperty).
- simpl in *; apply pr1.
- simpl in *; intros x; apply (pr2 x).
- apply (mk_isProductCone _ has_homsets_HSET).
  intros C f g; simpl in *.
  simple refine (tpair _ _ _).
  * apply (tpair _ (prodtofuntoprod (f ,, g))); split; apply idpath.
  * intros h; apply subtypeEquality.
    { abstract(intros x; apply isapropdirprod; apply has_homsets_HSET). }
    { abstract(destruct h as [t [ht1 ht2]]; simpl;
               apply funextfun; intro x;
               rewrite <- ht2, <- ht1; unfold compose; simpl;
               case (t x); intros; apply idpath). }
Defined.

Lemma ProductsHSET_from_Lims : Products HSET.
Proof.
exact (Products_from_Lims _ has_homsets_HSET LimsHSET).
Qed.

Lemma TerminalHSET : Terminal HSET.
Proof.
apply (mk_Terminal unitHSET).
apply mk_isTerminal; intro a.
apply (tpair _ (fun _ => tt)); simpl; intro f.
now apply funextfun; intro x; case (f x); apply idpath.
Defined.

Lemma TerminalHSET_from_Lims : Terminal HSET.
Proof.
now apply Terminal_from_Lims, LimsHSET.
Qed.

(*
Lemma PullbacksHSET : Pullbacks HSET.
Proof.
now apply Pullbacks_from_Lims, LimsHSET.
Qed.
*)