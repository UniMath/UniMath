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
- Pullbacks ([PullbacksHSET])
- Terminal object ([TerminalHSET])
- Exponentials ([has_exponentials_HSET])
- Construction of exponentials for functors into HSET
  ([has_exponentials_functor_HSET])

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
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.DiscretePrecategory.
Require Import UniMath.CategoryTheory.set_slice_fam_equiv.

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
use mk_cocone.
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

Lemma ColimsHSET_of_shape (g : graph) :
  Colims_of_shape g HSET.
Proof.
now intros d; apply ColimCoconeHSET.
Defined.

(* Direct construction of binary coproducts in HSET *)
Lemma BinCoproductsHSET : BinCoproducts HSET.
Proof.
intros A B.
use mk_BinCoproductCocone.
- simpl in *; apply (tpair _ (coprod A B)).
  abstract (apply isasetcoprod; apply setproperty).
- simpl in *; apply ii1.
- simpl in *; intros x; apply (ii2 x).
- apply (mk_isBinCoproductCocone _ has_homsets_HSET).
  intros C f g; simpl in *.
  mkpair.
  * apply (tpair _ (sumofmaps f g)); abstract (split; apply idpath).
  * abstract (intros h; apply subtypeEquality;
    [ intros x; apply isapropdirprod; apply has_homsets_HSET
    | destruct h as [t [ht1 ht2]]; simpl;
               apply funextfun; intro x;
               rewrite <- ht2, <- ht1; unfold compose; simpl;
               case x; intros; apply idpath]).
Defined.

Lemma CoproductsHSET (I : UU) (HI : isaset I) : Coproducts I HSET.
Proof.
intros A.
use mk_CoproductCocone.
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
now apply bincoproducts.BinCoproducts_from_Colims, ColimsHSET_of_shape.
Defined.

End CoproductsHSET_from_Colims.

Lemma InitialHSET : Initial HSET.
Proof.
apply (mk_Initial emptyHSET).
apply mk_isInitial; intro a.
mkpair.
- simpl; intro e; induction e.
- abstract (intro f; apply funextfun; intro e; induction e).
Defined.

Section InitialHSET_from_Colims.

Require UniMath.CategoryTheory.limits.graphs.initial.

Lemma InitialHSET_from_Colims : graphs.initial.Initial HSET.
Proof.
apply initial.Initial_from_Colims, ColimsHSET_of_shape.
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
use mk_LimCone.
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

Lemma LimsHSET_of_shape (g : graph) : Lims_of_shape g HSET.
Proof.
now intros d; apply LimConeHSET.
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
use mk_LimCone.
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

Lemma cats_LimsHSET_of_shape (g : precategory) : cats.limits.Lims_of_shape g HSET.
Proof.
now intros d; apply cats_LimConeHSET.
Defined.

(** end of alternative def *)

(** Direct construction of binary products in HSET *)
Lemma BinProductsHSET : BinProducts HSET.
Proof.
intros A B.
use mk_BinProductCone.
- simpl in *; apply (tpair _ (dirprod A B)).
  abstract (apply isasetdirprod; apply setproperty).
- simpl in *; apply pr1.
- simpl in *; intros x; apply (pr2 x).
- apply (mk_isBinProductCone _ has_homsets_HSET).
  intros C f g; simpl in *.
  mkpair.
  * apply (tpair _ (prodtofuntoprod (f ,, g))); abstract (split; apply idpath).
  * abstract (intros h; apply subtypeEquality;
    [ intros x; apply isapropdirprod; apply has_homsets_HSET
    | destruct h as [t [ht1 ht2]]; simpl; apply funextfun; intro x;
               rewrite <- ht2, <- ht1; unfold compose; simpl;
               unfold prodtofuntoprod;
               now case (t x)]).
Defined.

Lemma ProductsHSET (I : UU) : Products I HSET.
Proof.
intros A.
use mk_ProductCone.
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
now apply binproducts.BinProducts_from_Lims, LimsHSET_of_shape.
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
now apply terminal.Terminal_from_Lims, LimsHSET_of_shape.
Defined.

End TerminalHSET_from_Lims.

Definition PullbackHSET_ob {A B C : HSET} (f : HSET⟦B,A⟧) (g : HSET⟦C,A⟧) : HSET.
Proof.
simpl in *.
exists (Σ (xy : B × C), f (pr1 xy) = g (pr2 xy)).
abstract (apply isaset_total2; [ apply isasetdirprod; apply setproperty
                               | intros xy; apply isasetaprop, setproperty ]).
Defined.

Lemma PullbacksHSET : Pullbacks HSET.
Proof.
intros A B C f g.
use mk_Pullback.
+ apply (PullbackHSET_ob f g).
+ intros xy; apply (pr1 (pr1 xy)).
+ intros xy; apply (pr2 (pr1 xy)).
+ abstract (apply funextsec; intros [[x y] Hxy]; apply Hxy).
+ use mk_isPullback.
  intros X f1 f2 Hf12; cbn.
  use unique_exists.
  - intros x.
    exists (f1 x,,f2 x); abstract (apply (toforallpaths _ _ _ Hf12)).
  - abstract (now split).
  - abstract (now intros h; apply isapropdirprod; apply has_homsets_HSET).
  - abstract (intros h [H1 H2]; apply funextsec; intro x;
    apply subtypeEquality; [intros H; apply setproperty|]; simpl;
    now rewrite <- (toforallpaths _ _ _ H1 x), <- (toforallpaths _ _ _ H2 x), <- tppr).
Defined.

Section PullbacksHSET_from_Lims.

  Require UniMath.CategoryTheory.limits.graphs.pullbacks.

  Lemma PullbacksHSET_from_Lims : graphs.pullbacks.Pullbacks HSET.
  Proof.
    apply (graphs.pullbacks.Pullbacks_from_Lims HSET LimsHSET).
  Defined.

End PullbacksHSET_from_Lims.

Section EqualizersHSET_from_Lims.

  Require UniMath.CategoryTheory.limits.graphs.equalizers.

  Lemma EqualizersHSET_from_Lims : graphs.equalizers.Equalizers HSET.
  Proof.
    apply (graphs.equalizers.Equalizers_from_Lims HSET LimsHSET).
  Defined.

End EqualizersHSET_from_Lims.

Section exponentials.

(** Define the functor: A -> _^A *)
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

(** This checks that if we use constprod_functor2 the flip is not necessary *)
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
  [ intro x; simpl; apply funextfun; intro ax; now rewrite (tppr ax)
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
  [ now intro x; simpl; apply funextfun; intro ax; rewrite (tppr ax)
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
        apply (nat_trans_eq has_homsets_HSET); cbn; unfold prodtofuntoprod; intro x;
        apply funextsec; intro f;
        destruct f as [cx Px]; simpl; unfold covyoneda_morphisms_data;
        now rewrite id_left
      | intros a b c f g; simpl; apply funextsec; intro alpha;
        apply (nat_trans_eq has_homsets_HSET); cbn; unfold prodtofuntoprod; intro x;
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
  use (theta c).
  exact (identity c,,y).
- abstract (
    intros c c' f; simpl;
    apply funextfun; intros ytheta; destruct ytheta as [y theta];
    cbn; unfold prodtofuntoprod;
    unfold covyoneda_morphisms_data;
    assert (X := nat_trans_ax theta);
    assert (Y := toforallpaths _ _ _ (X c c' f) (identity c,, y));
    eapply pathscomp0; [|apply Y]; cbn; unfold prodtofuntoprod;
    now rewrite id_right, id_left).
Defined.

(* This could be made nicer without the big abstract blocks... *)
Lemma has_exponentials_functor_HSET : has_exponentials CP.
Proof.
intro P.
use left_adjoint_from_partial.
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
              intros a b f; simpl; cbn; unfold prodtofuntoprod;
              apply funextsec; intro x;
              eapply pathscomp0;
              [|apply (toforallpaths _ _ _ (nat_trans_ax φ _ _ f)
                                     (dirprodpair (pr2 x) (# R (pr1 x) u)))]; cbn;
              unfold prodtofuntoprod;
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
    unfold prodtofuntoprod;
    now rewrite id_right).
Qed.

End exponentials_functor_cat.

(** * Set is locally cartesian closed *)
Section locally_CCC.

Local Notation "HSET / X" := (slice_precat HSET X has_homsets_HSET).

Lemma Terminal_HSET_slice X : Terminal (HSET / X).
Proof.
now apply Terminal_slice_precat.
Defined.

Lemma BinProducts_HSET_slice X : BinProducts (HSET / X).
Proof.
now apply BinProducts_slice_precat, PullbacksHSET.
Defined.


(* Try to prove that Set/X has exponentials it using the equivalence to [X,Set] *)
Section via_equivalence.

Context (X : HSET).

Let discreteX : precategory := discrete_precategory (pr1 X).
Local Lemma has_homsets_discreteX : has_homsets discreteX.
Proof.
now apply has_homsets_discrete_precategory, hlevelntosn, setproperty.
Qed.

Local Notation "'[X,HSET]'" := ([discreteX, HSET, has_homsets_HSET]).
Local Lemma has_homsets_XHSET : has_homsets [X,HSET].
Proof.
apply functor_category_has_homsets.
Qed.

Let F : functor [X,HSET] (HSET / X) := fam_to_slice X.
Let α : adj_equivalence_of_precats F := set_slice_fam_equiv X.
Let Finv : functor (HSET / X) [X,HSET] := adj_equivalence_inv α.
Let eta := unit_iso_from_adj_equivalence_of_precats has_homsets_XHSET α.
Let eps := counit_iso_from_adj_equivalence_of_precats (has_homsets_slice_precat _ _ X) α.
(* Let eta' := unit_pointwise_iso_from_adj_equivalence α. *)
(* Let eps' := counit_pointwise_iso_from_adj_equivalence α. *)

Local Lemma BinProducts_XHSET : BinProducts [X,HSET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Lemma has_exponentials_XHSET : has_exponentials BinProducts_XHSET.
Proof.
apply has_exponentials_functor_HSET, has_homsets_discreteX.
Defined.

Lemma has_exponentials_HSET_slice_via_equiv : has_exponentials (BinProducts_HSET_slice X).
Proof.
intros Y.
set (H := has_exponentials_XHSET (Finv Y)).
set (H1:= pr1 H).
set (eta1 := pr1 (pr1 (pr2 H))).
exists (functor_composite (functor_composite Finv H1) F).
use mk_are_adjoints.
- admit.
- admit.
- admit.
Admitted.

End via_equivalence.

(* This is now hfiber_hSet *)
Definition hfiber_HSET {X Y} (f : HSET⟦X,Y⟧) (y : pr1 Y) : HSET.
Proof.
mkpair.
+ apply (hfiber f y).
+ abstract (now apply isaset_hfiber; apply setproperty).
Defined.

Definition hfiber_fun (X : HSET) (f : HSET / X) : HSET / X → HSET / X.
Proof.
intros g.
mkpair.
- exists (Σ x, HSET⟦hfiber_HSET (pr2 f) x,hfiber_HSET (pr2 g) x⟧).
  abstract (apply isaset_total2; [ apply setproperty | intros x; apply has_homsets_HSET ]).
- now apply pr1.
Defined.

Lemma PullbackArrowUnique' {C : precategory} {a b c : C} (f : C⟦b,a⟧) (g : C⟦c,a⟧)
      (P : Pullback f g) e (h : C⟦e,b⟧) (k : C⟦e,c⟧)
      (Hcomm : h ;; f = k ;; g) (w : C⟦e,P⟧) (H1 : w ;; PullbackPr1 P = h) (H2 : w ;; PullbackPr2 P = k) :
  w = PullbackArrow P e h k Hcomm.
Proof.
now apply PullbackArrowUnique.
Qed.

Definition hfiber_functor (X : HSET) (f : HSET / X) :
  functor (HSET / X) (HSET / X).
Proof.
use mk_functor.
+ mkpair.
  * apply (hfiber_fun _ f).
  * simpl; intros a b g.
    { mkpair; simpl.
    - intros h.
      exists (pr1 h).
      intros fx.
      mkpair.
      * apply (pr1 g), (pr1 (pr2 h fx)).
      * abstract (etrans; [ apply (!toforallpaths _ _ _ (pr2 g) (pr1 (pr2 h fx)))|];
                  apply (pr2 (pr2 h fx))).
    - abstract (now apply funextsec).
    }
+ abstract (split;
            [ intros x; apply (eq_mor_slicecat _ has_homsets_HSET); simpl;
              apply funextsec; intro y; simpl;
              destruct y as [y hy]; use total2_paths; [ apply idpath |];
              apply funextsec; intros w; apply subtypeEquality; [|apply idpath];
              now intros XX; apply setproperty
            | intros x y z g h; apply (eq_mor_slicecat _ has_homsets_HSET); simpl;
              apply funextsec; intro w; simpl;
              destruct w as [w hw];
              use total2_paths; [ apply idpath |];
              apply funextsec; intros w'; apply subtypeEquality; [|apply idpath];
              now intros XX; apply setproperty ]).
Defined.

(* Attempted direct proof using explicit formula in example 2.2 of:
    https://ncatlab.org/nlab/show/locally+cartesian+closed+category#in_category_theory
*)
Lemma has_exponentials_HSET_slice_direct (X : HSET) :
  has_exponentials (BinProducts_HSET_slice X).
Proof.
intros f.
exists (hfiber_functor _ f).
use mk_are_adjoints.
- use mk_nat_trans.
  + intros g.
    simpl.
    mkpair.
    * intros y. simpl.
      exists (pr2 g y).
      intros fgy.
      exists ((pr1 fgy,,y),,(pr2 fgy)).
      apply (pr2 fgy).
    * abstract (now apply funextsec).
  + intros g h w.
    apply (eq_mor_slicecat _ has_homsets_HSET).
    apply funextsec; intro x1.
    use total2_paths2.
    * apply (toforallpaths _ _ _ (!pr2 w) x1).
    * apply funextsec; intro y.
      simpl.
      admit. (* stuck *)
- admit.
- admit.
Admitted.


(* Attempted proof using proposition 2.1 from:
     https://ncatlab.org/nlab/show/locally+cartesian+closed+category#in_category_theory
*)
Definition product_hfiber_slice
  C C' (g : HSET ⟦C,C'⟧) (f : HSET / C) : HSET / C'.
Proof.
exists (total2_hSet (λ (c' : pr1 C'), forall_hSet (λ (c : Σ (c : pr1 C), g c = c'), hfiber_hSet (pr2 f) (pr1 c)))).
simpl; apply pr1.
Defined.

Lemma has_exponentials_HSET_slice : Π X, has_exponentials (BinProducts_HSET_slice X).
Proof.
use dependent_product_to_exponentials.
intros C C' g.
mkpair.
- use mk_functor.
  + mkpair.
    * intros f.
      apply (product_hfiber_slice C C' g f).
    * simpl; intros x y f. {
      mkpair.
      - intros Hc'.
        exists (pr1 Hc').
        intros p.
        exists (pr1 f (pr1 (pr2 Hc' p))).
        abstract (now rewrite <- (pr2 (pr2 Hc' p));
                      apply (toforallpaths _ _ _ (!pr2 f))).
      - abstract (now apply funextfun; intro z).
      }
  + abstract (split;
      [ intros x; simpl; apply subtypeEquality; [ intros ?; apply has_homsets_HSET|]; simpl;
        apply funextfun; intros [c' Hc']; apply (total2_paths2 (idpath _));
        rewrite idpath_transportf; apply funextsec; intro y;
        now apply subtypeEquality; [ intros ?; apply setproperty| apply idpath]
      | intros x y z f1 f2; simpl; apply subtypeEquality; [ intros ?; apply has_homsets_HSET|]; simpl;
        apply funextfun; intros [c' Hc']; apply (total2_paths2 (idpath _));
        rewrite idpath_transportf; apply funextsec; intro H;
        now apply subtypeEquality; [ intros xx; apply setproperty| apply idpath]]).
- use mk_are_adjoints.
  + use mk_nat_trans.
    * intros X; cbn. {
      mkpair.
      + simpl; intros x.
        exists (pr2 X x).
        intros H.
        mkpair.
        * exists (pr1 H,,x).
          abstract (apply (pr2 H)).
        * abstract (apply idpath).
      + abstract (apply idpath).
      }
    * intros x y f.
      apply eq_mor_slicecat.
      apply funextsec; intro w.
      use total2_paths2.
      apply (!(toforallpaths _ _ _ (pr2 f) w)).
      apply funextsec; intros w2.
      admit. (* stuck again *)
+ admit.
+ admit.
Admitted.

End locally_CCC.