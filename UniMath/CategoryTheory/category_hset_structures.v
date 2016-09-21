(** **********************************************************

Structures on HSET.

Contents:

- Colimits in HSET ([ColimsHSET])
- Binary coproducts ([BinCoproductsHSET])
- General indexed coproducts ([Coproducts_HSET])
- Initial object ([InitialHSET])
- Limits ([LimsHSET])
- Binary products ([BinProductsHSET])
- General indexed products ([ProductsHSET]
- Terminal object ([TerminalHSET])
- Exponentials ([has_exponentials_HSET])
- Construction of exponentials for functors into HSET ([has_exponentials_functor_HSET])

Written by: Benedikt Ahrens, Anders Mörtberg

October 2015 - January 2016

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.covyoneda.

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

(* This should be moved upstream. Constructs the smallest eqrel
   containing a given relation *)
Section extras.

Variable A : UU.
Variable R0 : hrel A.

Lemma isaprop_eqrel_from_hrel a b :
  isaprop (Π R : eqrel A, (Π x y, R0 x y -> R x y) -> R a b).
Proof.
  apply impred; intro R; apply impred_prop.
Qed.

Definition eqrel_from_hrel : hrel A :=
  fun a b => hProppair _ (isaprop_eqrel_from_hrel a b).

Lemma iseqrel_eqrel_from_hrel : iseqrel eqrel_from_hrel.
Proof.
repeat split.
- intros x y z H1 H2 R HR. exact (eqreltrans _ _ _ _ (H1 _ HR) (H2 _ HR)).
- now intros x R _; apply (eqrelrefl R).
- intros x y H R H'. exact (eqrelsymm _ _ _ (H _ H')).
Qed.

Lemma eqrel_impl a b : R0 a b -> eqrel_from_hrel a b.
Proof.
now intros H R HR; apply HR.
Qed.

(* eqrel_from_hrel is the *smallest* relation containing R0 *)
Lemma minimal_eqrel_from_hrel (R : eqrel A) (H : Π a b, R0 a b -> R a b) :
  Π a b, eqrel_from_hrel a b -> R a b.
Proof.
now intros a b H'; apply (H' _ H).
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
abstract (
repeat split;
[ intros x y z H1 H2 ;
  exact (pathscomp0 H1 H2)
|
  intros x y H;
  exact (pathsinv0 H)
]).
Defined.

Lemma rel0_impl a b (Hab : rel0 a b) : from_cobase_eqrel a b.
Proof.
refine (Hab _ _). clear Hab.
intro H; simpl.
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
  Σ x : HSET ⟦ colimHSET, c ⟧, Π v : vertex g, injections v ;; x = coconeIn cc v.
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
Defined.

End colimits.

Opaque from_colimHSET.

Lemma ColimsHSET : Colims HSET.
Proof.
now intros g d; apply ColimCoconeHSET.
Defined.

(* Direct construction of binary coproducts in HSET *)
Lemma BinCoproductsHSET : BinCoproducts HSET.
Proof.
intros A B.
simple refine (mk_BinCoproductCocone _ _ _ _ _ _ _).
- simpl in *; apply (tpair _ (coprod A B)).
  abstract (apply isasetcoprod; apply setproperty).
- simpl in *; apply ii1.
- simpl in *; intros x; apply (ii2 x).
- apply (mk_isBinCoproductCocone _ has_homsets_HSET).
  intros C f g; simpl in *.
  simple refine (tpair _ _ _).
  * apply (tpair _ (sumofmaps f g)); abstract (split; apply idpath).
  * abstract (intros h; apply subtypeEquality;
    [ intros x; apply isapropdirprod; apply has_homsets_HSET
    | destruct h as [t [ht1 ht2]]; simpl;
               apply funextfun; intro x;
               rewrite <- ht2, <- ht1; unfold compose; simpl;
               case x; intros; apply idpath]).
Defined.

Lemma Coproducts_HSET (I : UU) (HI : isaset I) : Coproducts I HSET.
Proof.
intros A.
simple refine (mk_CoproductCocone _ _ _ _ _ _).
- mkpair.
  + apply (Σ i, pr1 (A i)).
  + eapply (isaset_total2 _ HI); intro i; apply setproperty.
- simpl; apply tpair.
- apply (mk_isCoproductCocone _ _ has_homsets_HSET).
  intros C f; simpl in *.
  mkpair.
  * apply (tpair _ (fun X => f (pr1 X) (pr2 X))); abstract (intro i; apply idpath).
  * abstract (intros h; apply subtypeEquality; simpl;
      [ intro; apply impred; intro; apply has_homsets_HSET
      | destruct h as [t ht]; simpl; apply funextfun;
        intro x; rewrite <- ht; destruct x; apply idpath]).
Defined.

Section CoproductsHSET_from_Colims.

Require UniMath.CategoryTheory.limits.graphs.bincoproducts.

Lemma BinCoproductsHSET_from_Colims : graphs.bincoproducts.BinCoproducts HSET.
Proof.
exact (bincoproducts.BinCoproducts_from_Colims _ ColimsHSET).
Defined.

End CoproductsHSET_from_Colims.

Lemma InitialHSET : Initial HSET.
Proof.
apply (mk_Initial emptyHSET).
apply mk_isInitial; intro a.
simple refine (tpair _ _ _).
- simpl; intro e; induction e.
- abstract (intro f; apply funextfun; intro e; induction e).
Defined.

Section InitialHSET_from_Colims.

Require UniMath.CategoryTheory.limits.graphs.initial.

Lemma InitialHSET_from_Colims : graphs.initial.Initial HSET.
Proof.
now apply initial.Initial_from_Colims, ColimsHSET.
Defined.

End InitialHSET_from_Colims.

Section limits.

Variable g : graph.
Variable D : diagram g HSET.

Definition limset_UU : UU :=
  Σ (f : Π u : vertex g, pr1hSet (dob D u)),
    Π u v (e : edge u v), dmor D e (f u) = f v.

Definition limset : HSET.
Proof.
  exists limset_UU.
  apply (isofhleveltotal2 2);
            [ apply impred; intro; apply pr2
            | intro f; repeat (apply impred; intro);
              apply isasetaprop, setproperty ].
Defined.

Lemma LimConeHSET : LimCone D.
Proof.
simple refine (mk_LimCone _ _ _ _ ).
- apply limset.
- apply (tpair _ (fun u f => pr1 f u)).
  abstract (intros u v e; simpl; apply funextfun; intro f; simpl; apply (pr2 f)).
- intros X CC.
  mkpair.
  + mkpair.
    * intro x; apply (tpair _ (fun u => coneOut CC u x)).
      abstract (intros u v e; apply (toforallpaths _ _ _ (coneOutCommutes CC _ _ e))).
    * abstract (intro v; apply idpath).
  + abstract (intros [t p]; apply subtypeEquality;
              [ intro; apply impred; intro; apply isaset_set_fun_space
              | apply funextfun; intro; apply subtypeEquality];
                [ intro; repeat (apply impred; intro); apply setproperty
                | apply funextsec; intro u; apply (toforallpaths _ _ _ (p u))]).
Defined.

End limits.

Lemma LimsHSET : Lims HSET.
Proof.
now intros g d; apply LimConeHSET.
Defined.

(** Alternative definition of limits using cats/limits *)
Section cats_limits.

Require UniMath.CategoryTheory.limits.cats.limits.

Variable J : precategory.
Variable D : functor J HSET.

Definition cats_limset_UU : UU :=
  Σ (f : Π u, pr1hSet (D u)),
    Π u v (e : J⟦u,v⟧), # D e (f u) = f v.

Definition cats_limset : HSET.
Proof.
  exists cats_limset_UU.
  apply (isofhleveltotal2 2);
            [ apply impred; intro; apply pr2
            | intro f; repeat (apply impred; intro);
              apply isasetaprop, setproperty ].
Defined.

Lemma cats_LimConeHSET : cats.limits.LimCone D.
Proof.
simple refine (mk_LimCone _ _ _ _ ).
- apply cats_limset.
- apply (tpair _ (fun u f => pr1 f u)).
  abstract (intros u v e; apply funextfun; intro f; apply (pr2 f)).
- intros X CC.
  mkpair.
  + mkpair.
    * intro x; apply (tpair _ (fun u => coneOut CC u x)).
      abstract (intros u v e; apply (toforallpaths _ _ _ (coneOutCommutes CC _ _ e))).
    * abstract (intro v; apply idpath).
  + abstract (intros [t p]; apply subtypeEquality;
     [ intro; apply impred; intro; apply isaset_set_fun_space
     | apply funextfun; intro x; apply subtypeEquality];
       [ intro; repeat (apply impred; intro); apply setproperty
       | simpl; apply funextsec; intro u; apply (toforallpaths _ _ _ (p u))]).
Defined.

End cats_limits.

Lemma cats_LimsHSET : cats.limits.Lims HSET.
Proof.
now intros g d; apply cats_LimConeHSET.
Defined.

(** end of alternative def *)

(* Direct construction of binary products in HSET *)
Lemma BinProductsHSET : BinProducts HSET.
Proof.
intros A B.
simple refine (mk_BinProductCone _ _ _ _ _ _ _).
- simpl in *; apply (tpair _ (dirprod A B)).
  abstract (apply isasetdirprod; apply setproperty).
- simpl in *; apply pr1.
- simpl in *; intros x; apply (pr2 x).
- apply (mk_isBinProductCone _ has_homsets_HSET).
  intros C f g; simpl in *.
  simple refine (tpair _ _ _).
  * apply (tpair _ (prodtofuntoprod (f ,, g))); abstract (split; apply idpath).
  * abstract (intros h; apply subtypeEquality;
    [ intros x; apply isapropdirprod; apply has_homsets_HSET
    | destruct h as [t [ht1 ht2]]; simpl; apply funextfun; intro x;
               rewrite <- ht2, <- ht1; unfold compose; simpl;
               unfold prodtofuntoprod;
               now case (t x)]).
Defined.

Lemma Products_HSET (I : UU) : Products I HSET.
Proof.
intros A.
simple refine (mk_ProductCone _ _ _ _ _ _).
- apply (tpair _ (Π i, pr1 (A i))); apply isaset_forall_hSet.
- simpl; intros i f; apply (f i).
- apply (mk_isProductCone _ _ has_homsets_HSET).
  intros C f; simpl in *.
  mkpair.
  * apply (tpair _ (fun c i => f i c)); intro i; apply idpath.
   * abstract (intros h; apply subtypeEquality; simpl;
       [ intro; apply impred; intro; apply has_homsets_HSET
       | destruct h as [t ht]; simpl; apply funextfun; intro x;
         apply funextsec; intro i; rewrite <- ht; apply idpath ]).
Defined.

Section BinProductsHSET_from_Lims.

Require UniMath.CategoryTheory.limits.graphs.binproducts.

Lemma BinProductsHSET_from_Lims : graphs.binproducts.BinProducts HSET.
Proof.
exact (binproducts.BinProducts_from_Lims _ LimsHSET).
Defined.

End BinProductsHSET_from_Lims.

Lemma TerminalHSET : Terminal HSET.
Proof.
apply (mk_Terminal unitHSET).
apply mk_isTerminal; intro a.
apply (tpair _ (fun _ => tt)).
abstract (simpl; intro f; apply funextfun; intro x; case (f x); apply idpath).
Defined.

Section TerminalHSET_from_Lims.

Require UniMath.CategoryTheory.limits.graphs.terminal.

Lemma TerminalHSET_from_Lims : graphs.terminal.Terminal HSET.
Proof.
now apply terminal.Terminal_from_Lims, LimsHSET.
Defined.

End TerminalHSET_from_Lims.

(*
Lemma PullbacksHSET : Pullbacks HSET.
Proof.
now apply Pullbacks_from_Lims, LimsHSET.
Qed.
*)

Section exponentials.

(* Define the functor: A -> _^A *)
Definition exponential_functor (A : HSET) : functor HSET HSET.
Proof.
mkpair.
+ apply (tpair _ (hset_fun_space A)); simpl.
  intros b c f g; apply (fun x => f (g x)).
+ abstract (mkpair;
  [ intro x; now (repeat apply funextfun; intro)
  | intros x y z f g; now (repeat apply funextfun; intro)]).
Defined.

Definition flip {A B C : UU} (f : A -> B -> C) : B -> A -> C := fun x y => f y x.

Lemma paireta {A B : UU} (p : A × B) : p = (pr1 p,, pr2 p).
Proof.
destruct p; apply idpath.
Defined.

(* This checks that if we use constprod_functor2 the flip is not necessary *)
Lemma are_adjoints_constprod_functor2 A :
  are_adjoints (constprod_functor2 BinProductsHSET A) (exponential_functor A).
Proof.
mkpair.
- mkpair.
  + mkpair.
    * intro x; simpl; apply dirprodpair.
    * abstract (intros x y f; apply idpath).
  + mkpair.
    * intros X fx; apply (pr1 fx (pr2 fx)).
    * abstract (intros x y f; apply idpath).
- abstract (mkpair;
  [ intro x; simpl; apply funextfun; intro ax; now rewrite (paireta ax)
  | intro b; apply funextfun; intro f; apply idpath]).
Defined.

Lemma has_exponentials_HSET : has_exponentials BinProductsHSET.
Proof.
intro a.
apply (tpair _ (exponential_functor a)).
mkpair.
- mkpair.
  + mkpair.
    * intro x; simpl; apply flip, dirprodpair.
    * abstract (intros x y f; apply idpath).
  + mkpair.
    * intros x xf; simpl in *; apply (pr2 xf (pr1 xf)).
    * abstract (intros x y f; apply idpath).
- abstract (mkpair;
  [ now intro x; simpl; apply funextfun; intro ax; rewrite (paireta ax)
  | now intro b; apply funextfun; intro f]).
Defined.

End exponentials.

(** This section defines exponential in [C,HSET] following a slight
variation of Moerdijk-MacLane (p. 46, Prop. 1).

The formula for [C,Set] is G^F(f)=Hom(Hom(f,−)×id(F),G) taken from:

http://mathoverflow.net/questions/104152/exponentials-in-functor-categories
*)
Section exponentials_functor_cat.

Variable (C : precategory) (hsC : has_homsets C).

Let CP := BinProducts_functor_precat C _ BinProductsHSET has_homsets_HSET.
Let cy := covyoneda _ hsC.

(* Defined Q^P *)
Local Definition exponential_functor_cat (P Q : functor C HSET) : functor C HSET.
Proof.
mkpair.
- mkpair.
  + intro c.
    use hSetpair.
    * apply (nat_trans (BinProduct_of_functors C _ BinProductsHSET (cy c) P) Q).
    * abstract (apply (isaset_nat_trans has_homsets_HSET)).
  + simpl; intros a b f alpha.
    apply (BinProductOfArrows _ (CP (cy a) P) (CP (cy b) P)
                           (# cy f) (identity _) ;; alpha).
- abstract (
    split;
      [ intros c; simpl; apply funextsec; intro a;
        apply (nat_trans_eq has_homsets_HSET); cbn; intro x;
        apply funextsec; intro f;
        destruct f as [cx Px]; simpl; unfold covyoneda_morphisms_data;
        now rewrite id_left
      | intros a b c f g; simpl; apply funextsec; intro alpha;
        apply (nat_trans_eq has_homsets_HSET); cbn; intro x;
        apply funextsec; intro h;
        destruct h as [cx pcx]; simpl; unfold covyoneda_morphisms_data;
        now rewrite assoc ]).
Defined.

Local Definition eval (P Q : functor C HSET) :
 nat_trans (BinProductObject _ (CP P (exponential_functor_cat P Q)) : functor _ _) Q.
Proof.
mkpair.
- intros c ytheta; set (y := pr1 ytheta); set (theta := pr2 ytheta);
  simpl in *.
  apply (theta c).
  apply (identity c,,y).
- abstract (
    intros c c' f; simpl;
    apply funextfun; intros ytheta; destruct ytheta as [y theta]; cbn;
    unfold covyoneda_morphisms_data;
    assert (X := nat_trans_ax theta);
    assert (Y := toforallpaths _ _ _ (X c c' f) (identity c,, y));
    eapply pathscomp0; [|apply Y]; cbn;
    now rewrite id_right, id_left).
Defined.

(* This could be made nicer without the big abstract blocks... *)
Lemma has_exponentials_functor_HSET : has_exponentials CP.
Proof.
intro P.
use adjunction_from_partial.
- apply (exponential_functor_cat P).
- intro Q; simpl; apply eval.
- intros Q R φ; simpl in *.
  mkpair.
  + mkpair.
    * { mkpair.
        - intros c u; simpl.
          mkpair.
          + simpl; intros d fx.
            apply (φ d (dirprodpair (pr2 fx) (# R (pr1 fx) u))).
          + abstract (
              intros a b f; simpl; cbn;
              apply funextsec; intro x;
              eapply pathscomp0;
              [|apply (toforallpaths _ _ _ (nat_trans_ax φ _ _ f)
                                     (dirprodpair (pr2 x) (# R (pr1 x) u)))]; cbn;
              apply maponpaths, maponpaths;
              assert (H : # R (pr1 x ;; f) = # R (pr1 x) ;; #R f);
              [apply functor_comp|];
              apply (toforallpaths _ _ _ H u)).
        - abstract (
            intros a b f; cbn;
            apply funextsec; intros x; cbn; simpl;
            apply subtypeEquality;
            [intros xx; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|];
            simpl; apply funextsec; intro y; cbn;
            apply funextsec; intro z;
            apply maponpaths, maponpaths;
            unfold covyoneda_morphisms_data;
            assert (H : # R (f ;; pr1 z) = # R f ;; # R (pr1 z));
              [apply functor_comp|];
            apply pathsinv0;
            now eapply pathscomp0; [apply (toforallpaths _ _ _ H x)|]).
      }
    * abstract (
        apply (nat_trans_eq has_homsets_HSET); cbn; intro x;
        apply funextsec; intro p;
        apply maponpaths;
        assert (H : # R (identity x) = identity (R x));
          [apply functor_id|];
        induction p as [t p]; apply maponpaths; simpl;
        now apply pathsinv0; eapply pathscomp0; [apply (toforallpaths _ _ _ H p)|]).
  + abstract (
    intros [t p]; apply subtypeEquality; simpl;
    [intros x; apply (isaset_nat_trans has_homsets_HSET)|];
    apply (nat_trans_eq has_homsets_HSET); intros c;
    apply funextsec; intro rc;
    apply subtypeEquality;
    [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]; simpl;
    rewrite p; cbn; clear p; apply funextsec; intro d; cbn;
    apply funextsec; intros [t0 pd]; simpl;
    assert (HH := toforallpaths _ _ _ (nat_trans_ax t c d t0) rc);
    cbn in HH; rewrite HH; cbn; unfold covyoneda_morphisms_data;
    now rewrite id_right).
Qed.

End exponentials_functor_cat.