(**

This file contains theory about (omega-) cocontinuous functors, i.e. functors which preserve
(sequential-) colimits ([is_omega_cocont] and [is_cocont]).

The main result is Adámek's theorem for constructing initial algebras of omega-cocontinuous functors
([colimAlgIsInitial]) which is used to construct inductive types.

This file also contains proofs that the following functors are (omega-)cocontinuous:

- Identity functor
  [is_cocont_functor_identity] [is_omega_cocont_functor_identity]
- Constant functor: F_x : C -> D, c |-> x
  [is_omega_cocont_constant_functor]
- Composition of omega-cocontinuous functors
  [is_cocont_functor_composite] [is_omega_cocont_functor_composite]
- Iteration of omega-cocontinuous functors: F^n : C -> C
  [is_cocont_iter_functor] [is_omega_cocont_iter_functor]
- Pairing of (omega-)cocont functors (F,G) : A * B -> C * D, (x,y) |-> (F x,G y)
  [is_cocont_pair_functor] [is_omega_cocont_pair_functor]
- Indexed families of (omega-)cocont functors F^I : A^I -> B^I
  [is_cocont_family_functor] [is_omega_cocont_family_functor]
- Binary delta functor: C -> C^2, x |-> (x,x)
  [is_cocont_bindelta_functor] [is_omega_cocont_bindelta_functor]
- General delta functor: C -> C^I
  [is_cocont_delta_functor] [is_omega_cocont_delta_functor]
- Binary coproduct functor: C^2 -> C, (x,y) |-> x + y
  [is_cocont_bincoproduct_functor] [is_omega_cocont_bincoproduct_functor]
- General coproduct functor: C^I -> C
  [is_cocont_coproduct_functor] [is_omega_cocont_coproduct_functor]
- Binary coproduct of functors: F + G : C -> D, x |-> F x + G x
  [is_cocont_BinCoproduct_of_functors_alt] [is_omega_cocont_BinCoproduct_of_functors_alt]
  [is_cocont_BinCoproduct_of_functors_alt2] [is_omega_cocont_BinCoproduct_of_functors_alt2]
  [is_cocont_BinCoproduct_of_functors] [is_omega_cocont_BinCoproduct_of_functors]
- Coproduct of families of functors: + F_i : C -> D  (generalization of coproduct of functors)
  [is_cocont_coproduct_of_functors_alt] [is_cocont_coproduct_of_functors]
  [is_omega_cocont_coproduct_of_functors_alt] [is_omega_cocont_coproduct_of_functors]
- Constant product functors: C -> C, x |-> a * x  and  x |-> x * a
  [is_cocont_constprod_functor1] [is_cocont_constprod_functor2]
  [is_omega_cocont_constprod_functor1] [is_omega_cocont_constprod_functor2]
- Binary product functor: C^2 -> C, (x,y) |-> x * y
  [is_omega_cocont_binproduct_functor]
- Product of functors: F * G : C -> D, x |-> (x,x) |-> (F x,G x) |-> F x * G x
  [is_omega_cocont_BinProduct_of_functors_alt] [is_omega_cocont_BinProduct_of_functors]
- Precomposition functor: _ o K : ⟦C,A⟧ -> ⟦M,A⟧ for K : M -> C
  [preserves_colimit_pre_composition_functor] [is_omega_cocont_pre_composition_functor]
- Postcomposition with a left adjoint:
  [is_cocont_post_composition_functor] [is_omega_cocont_post_composition_functor]
- Swapping of functor category arguments:
  [is_cocont_functor_cat_swap] [is_omega_cocont_functor_cat_swap]
- The forgetful functor from Set/X to Set preserves colimits
  ([preserves_colimit_slicecat_to_cat_HSET])

Written by: Anders Mörtberg and Benedikt Ahrens, 2015-2016

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.slicecat.

Local Open Scope cat.

(** * Definition of cocontinuous functors *)
Section cocont.

Context {C D : precategory} (F : functor C D).

Definition is_cocont : UU := ∏ {g : graph} (d : diagram g C) (L : C)
  (cc : cocone d L), preserves_colimit F d L cc.

End cocont.

(** * Definition of chains and omega-cocontinuous functors *)
Section omega_cocont.

(** Define the chain:
<<
     0 --> 1 --> 2 --> 3 --> ...
>>
   with exactly one arrow from n to S n.
*)

Definition nat_graph : graph :=
  mk_graph nat (λ m n, 1 + m = n).

Local Notation "'chain'" := (diagram nat_graph).

Definition mapchain {C D : precategory} (F : functor C D)
  (c : chain C) : chain D := mapdiagram F c.

(** Any i < j gives a morphism in the chain *)
Definition chain_mor {C : precategory} (c : chain C) {i j} :
  i < j -> C⟦dob c i, dob c j⟧.
Proof.
induction j as [|j IHj].
- intros Hi0.
  destruct (negnatlthn0 0 Hi0).
- intros Hij.
  destruct (natlehchoice4 _ _ Hij) as [|H].
  + apply (IHj h · dmor c (idpath (S j))).
  + apply dmor, (maponpaths S H).
Defined.

Lemma chain_mor_coconeIn {C : precategory} (c : chain C) (x : C)
  (cc : cocone c x) i : ∏ j (Hij : i < j),
  chain_mor c Hij · coconeIn cc j = coconeIn cc i.
Proof.
induction j as [|j IHj].
- intros Hi0.
  destruct (negnatlthn0 _ Hi0).
- intros Hij; simpl.
  destruct (natlehchoice4 _ _ Hij).
  + rewrite <- (IHj h), <- assoc.
    apply maponpaths, coconeInCommutes.
  + destruct p.
    apply coconeInCommutes.
Qed.

(** One of the hypotheses of this lemma is redundant, however when stated this way the lemma can be
used for any two proofs making it easier to apply. *)
Lemma chain_mor_right {C : precategory} {c : chain C} {i j} (Hij : i < j) (HSij : S i < j) :
  dmor c (idpath (S i)) · chain_mor c HSij = chain_mor c Hij.
Proof.
induction j as [|j IHj].
- destruct (negnatlthn0 _ Hij).
- simpl.
  destruct (natlehchoice4 _ _ Hij).
  + destruct (natlehchoice4 _ _ HSij).
    * now rewrite <- (IHj h h0), assoc.
    * destruct p; simpl.
      destruct (natlehchoice4 _ _ h); [destruct (isirreflnatlth _ h0)|].
      apply cancel_postcomposition, maponpaths, isasetnat.
  + destruct p, (isirreflnatlth _ HSij).
Qed.

(** See comment for [chain_mor_right] about the redundant hypothesis *)
Lemma chain_mor_left {C : precategory} {c : chain C} {i j} (Hij : i < j) (HiSj : i < S j) :
  chain_mor c Hij · dmor c (idpath (S j)) = chain_mor c HiSj.
Proof.
destruct j.
- destruct (negnatlthn0 _ Hij).
- simpl; destruct (natlehchoice4 i (S j) HiSj).
  + destruct (natlehchoice4 _ _ h).
    * destruct (natlehchoice4 _ _ Hij); [|destruct p, (isirreflnatlth _ h0)].
      apply cancel_postcomposition, cancel_postcomposition, maponpaths, isasetbool.
    * destruct p; simpl.
      destruct (natlehchoice4 _ _ Hij); [destruct (isirreflnatlth _ h0)|].
      apply cancel_postcomposition, maponpaths, isasetnat.
  + generalize Hij; rewrite p; intros H.
    destruct (isirreflnatlth _ H).
Qed.

(** Construct the chain:
<<
         !          F!            F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...
>>
*)
Definition initChain {C : precategory} (InitC : Initial C) (F : functor C C) : chain C.
Proof.
exists (λ n, iter_functor F n InitC).
intros m n Hmn. destruct Hmn. simpl.
induction m as [|m IHm]; simpl.
- exact (InitialArrow InitC _).
- exact (# F IHm).
Defined.

Definition is_omega_cocont {C D : precategory} (F : functor C D) : UU :=
  ∏ (c : chain C) (L : C) (cc : cocone c L),
  preserves_colimit F c L cc.

Definition omega_cocont_functor (C D : precategory) : UU :=
  ∑ (F : functor C D), is_omega_cocont F.

End omega_cocont.

Local Notation "'chain'" := (diagram nat_graph).


(** * Adámek's theorem for constructing initial algebras of omega-cocontinuous functors *)
(** This section proves that (L,α : F L -> L) is the initial algebra
    where L is the colimit of the inital chain:
<<
         !          F !           F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...
>>
This result is also known as Adámek's theorem % \cite{Adamek1974}: \par %

  https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor#AdameksTheorem

Adámek, Jiří. "Free algebras and automata realizations in the language of categories."
Commentationes Mathematicae Universitatis Carolinae 015.4 (1974): 589-602.

*)
Section colim_initial_algebra.

Context {C : precategory} (hsC : has_homsets C) (InitC : Initial C).

(* It is important that these are not packaged together as it is
   sometimes necessary to control how opaque HF is. See
   isalghom_pr1foldr in lists.v *)
Context {F : functor C C} (HF : is_omega_cocont F).

Let Fchain : chain C := initChain InitC F.

Variable (CC : ColimCocone Fchain).

Let L : C := colim CC.
Let FFchain : chain C := mapchain F Fchain.
Let Fa : cocone FFchain (F L) := mapcocone F _ (colimCocone CC).
Let FHC' : isColimCocone FFchain (F L) Fa :=
  HF Fchain L (colimCocone CC) (isColimCocone_from_ColimCocone CC).
Let FHC : ColimCocone FFchain := mk_ColimCocone _ _ _ FHC'.

Local Definition shiftCocone : cocone FFchain L.
Proof.
use mk_cocone.
- intro n; apply (coconeIn (colimCocone CC) (S n)).
- abstract (intros m n e; destruct e ;
            apply (coconeInCommutes (colimCocone CC) (S m) _ (idpath _))).
Defined.

Local Definition unshiftCocone (x : C) (cc : cocone FFchain x) : cocone Fchain x.
Proof.
use mk_cocone.
- simpl; intro n.
  induction n as [|n]; simpl.
  + apply InitialArrow.
  + apply (coconeIn cc _).
- abstract (simpl; intros m n e; destruct e;
            destruct m as [|m]; [ apply InitialArrowUnique
                                | apply (coconeInCommutes cc m _ (idpath _))]).
Defined.

Local Definition shiftIsColimCocone : isColimCocone FFchain L shiftCocone.
Proof.
intros x cc; simpl.
mkpair.
+ mkpair.
  * apply colimArrow, (unshiftCocone _ cc).
  * abstract (intro n; apply (colimArrowCommutes CC x (unshiftCocone x cc) (S n))).
+ abstract (intros p; apply subtypeEquality;
             [ intro f; apply impred; intro; apply hsC
             | apply colimArrowUnique; intro n;
               destruct n as [|n]; [ apply InitialArrowUnique | apply (pr2 p) ]]).
Defined.

Local Definition shiftColimCocone : ColimCocone FFchain :=
  mk_ColimCocone FFchain L shiftCocone shiftIsColimCocone.

Definition colim_algebra_mor : C⟦F L,L⟧ := colimArrow FHC L shiftCocone.

Local Definition is_iso_colim_algebra_mor : is_iso colim_algebra_mor :=
  isColim_is_iso _ FHC _ _ shiftIsColimCocone.

Let α : iso (F L) L := isopair _ is_iso_colim_algebra_mor.
Let α_inv : iso L (F L) := iso_inv_from_iso α.
Let α_alg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L α.

Lemma unfold_inv_from_iso_α :
  inv_from_iso α = colimArrow shiftColimCocone _ (colimCocone FHC).
Proof.
apply id_right.
Qed.

(** Given an algebra:
<<
          a
   F A ------> A
>>
 we now define an algebra morphism ad:
<<
          α
   F L ------> L
    |          |
    |          | ad
    |          |
    V     a    V
   F A ------> A
>>

*)
Section algebra_mor.

Variable (Aa : algebra_ob F).

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

Local Definition cocone_over_alg (n : nat) : C ⟦ dob Fchain n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn · a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

(* This makes Coq not unfold dmor during simpl *)
Arguments dmor : simpl never.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor Fchain e · an Sn = an n.
Proof.
destruct e.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- simpl; rewrite assoc.
  apply cancel_postcomposition, pathsinv0.
  eapply pathscomp0; [|simpl; apply functor_comp].
  now apply maponpaths, pathsinv0, IHn.
Qed.

(* ad = a† = a dagger *)
Local Definition ad : C⟦L,A⟧.
Proof.
apply colimArrow.
use mk_cocone.
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma ad_is_algebra_mor : is_algebra_mor _ α_alg Aa ad.
Proof.
apply pathsinv0, iso_inv_to_left, colimArrowUnique; simpl; intro n.
destruct n as [|n].
- now apply InitialArrowUnique.
- rewrite assoc, unfold_inv_from_iso_α.
  eapply pathscomp0;
    [apply cancel_postcomposition, (colimArrowCommutes shiftColimCocone)|].
  simpl; rewrite assoc, <- functor_comp.
  apply cancel_postcomposition, maponpaths, (colimArrowCommutes CC).
Qed.

Local Definition ad_mor : algebra_mor F α_alg Aa := tpair _ _ ad_is_algebra_mor.

End algebra_mor.

Lemma colimAlgIsInitial_subproof (Aa : FunctorAlg F hsC)
        (Fa' : algebra_mor F α_alg Aa) : Fa' = ad_mor Aa.
Proof.
apply (algebra_mor_eq _ hsC); simpl.
apply colimArrowUnique; simpl; intro n.
destruct Fa' as [f hf]; simpl.
unfold is_algebra_mor in hf; simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  apply cancel_postcomposition, pathsinv0, (iso_inv_to_right _ _ _ _ _ α).
  rewrite unfold_inv_from_iso_α; apply pathsinv0.
  now eapply pathscomp0; [apply (colimArrowCommutes shiftColimCocone)|].
Qed.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) α_alg.
Proof.
apply mk_isInitial; intros Aa.
exists (ad_mor Aa).
apply colimAlgIsInitial_subproof.
Defined.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  mk_Initial _ colimAlgIsInitial.

End colim_initial_algebra.


(** * Examples of (omega) cocontinuous functors *)
Section cocont_functors.

(** ** Left adjoints preserve colimits *)
Lemma left_adjoint_cocont {C D : precategory} (F : functor C D)
  (H : is_left_adjoint F) (hsC : has_homsets C) (hsD : has_homsets D) : is_cocont F.
Proof.
now intros g d L ccL; apply left_adjoint_preserves_colimit.
Defined.

(* Print Assumptions left_adjoint_cocont. *)

(** Cocontinuity is preserved by isomorphic functors *)
Section cocont_iso.

(* As this section is proving a proposition, the hypothesis can be weakened from a specified iso to
F and G being isomorphic. *)
Context {C D : precategory} (hsD : has_homsets D) {F G : functor C D}
        (αiso : @iso [C,D,hsD] F G).

Section preserves_colimit_iso.

Context {g : graph} (d : diagram g C) (L : C) (cc : cocone d L) (HF : preserves_colimit F d L cc).

Let αinv := inv_from_iso αiso.
Let α := pr1 αiso.
Let Hα : is_iso α := pr2 αiso.

Local Definition ccFy y (ccGy : cocone (mapdiagram G d) y) : cocone (mapdiagram F d) y.
Proof.
use mk_cocone.
- intro v; apply (pr1 α (dob d v) · coconeIn ccGy v).
- abstract (simpl; intros u v e; rewrite <- (coconeInCommutes ccGy u v e), !assoc;
            apply cancel_postcomposition, nat_trans_ax).
Defined.

Lemma αinv_f_commutes y (ccGy : cocone (mapdiagram G d) y) (f : D⟦F L,y⟧)
       (Hf : ∏ v,coconeIn (mapcocone F d cc) v · f = coconeIn (ccFy y ccGy) v) :
       ∏ v, # G (coconeIn cc v) · (pr1 αinv L · f) = coconeIn ccGy v.
Proof.
intro v; rewrite assoc.
eapply pathscomp0; [apply cancel_postcomposition, nat_trans_ax|].
rewrite <- assoc; eapply pathscomp0; [apply maponpaths, (Hf v)|]; simpl; rewrite assoc.
eapply pathscomp0.
  apply cancel_postcomposition.
  apply (nat_trans_eq_pointwise (@iso_after_iso_inv [C,D,hsD] _ _ (isopair _ Hα))).
now rewrite id_left.
Qed.

Lemma αinv_f_unique y (ccGy : cocone (mapdiagram G d) y) (f : D⟦F L,y⟧)
     (Hf : ∏ v,coconeIn (mapcocone F d cc) v · f = coconeIn (ccFy y ccGy) v)
     (HHf : ∏ t : ∑ x, ∏ v, coconeIn (mapcocone F d cc) v · x = coconeIn _ v, t = f,, Hf)
      f' (Hf' : ∏ v, # G (coconeIn cc v) · f' = coconeIn ccGy v) :
      f' = pr1 αinv L · f.
Proof.
transparent assert (HH : (∑ x : D ⟦ F L, y ⟧,
            ∏ v : vertex g,
            coconeIn (mapcocone F d cc) v · x = coconeIn (ccFy y ccGy) v)).
{ mkpair.
  - apply (pr1 α L · f').
  - abstract (intro v; rewrite <- Hf', !assoc; apply cancel_postcomposition, nat_trans_ax).
}
apply pathsinv0.
generalize (maponpaths pr1 (HHf HH)); intro Htemp; simpl in *.
rewrite <- Htemp; simpl; rewrite assoc.
eapply pathscomp0.
  apply cancel_postcomposition.
  apply (nat_trans_eq_pointwise (@iso_after_iso_inv [C,D,hsD] _ _ (isopair _ Hα))).
now apply id_left.
Qed.

Lemma preserves_colimit_iso  : preserves_colimit G d L cc.
Proof.
intros HccL y ccGy.
set (H := HF HccL y (ccFy y ccGy)).
set (f := pr1 (pr1 H)); set (Hf := pr2 (pr1 H)); set (HHf := pr2 H).
use unique_exists.
- apply (pr1 αinv L · f).
- simpl; apply (αinv_f_commutes y ccGy f Hf).
- abstract (intro; apply impred; intro; apply hsD).
- abstract (simpl in *; intros f' Hf'; apply (αinv_f_unique y ccGy f Hf); trivial;
            intro t; rewrite (HHf t); apply tppr).
Defined.

End preserves_colimit_iso.

Lemma is_cocont_iso : is_cocont F -> is_cocont G.
Proof.
now intros H g d c cc; apply (preserves_colimit_iso).
Defined.

Lemma is_omega_cocont_iso : is_omega_cocont F -> is_omega_cocont G.
Proof.
now intros H g d c cc; apply (preserves_colimit_iso).
Defined.

End cocont_iso.

(** ** The identity functor is (omega) cocontinuous *)
Section functor_identity.

Context {C : precategory} (hsC : has_homsets C).

Lemma preserves_colimit_identity {g : graph} (d : diagram g C) (L : C)
  (cc : cocone d L) : preserves_colimit (functor_identity C) d L cc.
Proof.
intros HcL y ccy; simpl.
set (CC := mk_ColimCocone _ _ _ HcL).
mkpair.
- mkpair.
  + apply (colimArrow CC), ccy.
  + abstract (simpl; intro n; apply (colimArrowCommutes CC)).
- abstract (simpl; intro t; apply subtypeEquality;
    [ simpl; intro v; apply impred; intro; apply hsC
    | apply (colimArrowUnique CC); intro n; apply (pr2 t)]).
Defined.

Lemma is_cocont_functor_identity : is_cocont (functor_identity C).
Proof.
now intros g; apply preserves_colimit_identity.
Defined.

Lemma is_omega_cocont_functor_identity : is_omega_cocont (functor_identity C).
Proof.
now intros c; apply is_cocont_functor_identity.
Defined.

Definition omega_cocont_functor_identity : omega_cocont_functor C C :=
  tpair _ _ is_omega_cocont_functor_identity.

End functor_identity.

(** ** The constant functor is omega cocontinuous *)
Section constant_functor.

Context {C D : precategory} (hsD : has_homsets D) (x : D).

(* Without the conn argument this is is too weak as diagrams are not necessarily categories *)
Lemma preserves_colimit_constant_functor {g : graph} (v : vertex g)
  (conn : ∏ (u : vertex g), edge v u)
  (d : diagram g C) (L : C) (cc : cocone d L) :
  preserves_colimit (constant_functor C D x) d L cc.
Proof.
intros HcL y ccy; simpl.
mkpair.
- apply (tpair _ (coconeIn ccy v)).
  abstract (now intro u; generalize (coconeInCommutes ccy _ _ (conn u));
            rewrite !id_left; intro H; rewrite H).
- abstract (intro p; apply subtypeEquality;
              [ intro; apply impred; intro; apply hsD
              | now destruct p as [p H]; rewrite <- (H v), id_left ]).
Defined.

(** The constant functor is omega cocontinuous *)
Lemma is_omega_cocont_constant_functor : is_omega_cocont (constant_functor C D x).
Proof.
intros c L ccL HccL y ccy.
mkpair.
- apply (tpair _ (coconeIn ccy 0)).
  abstract (intro n; rewrite id_left; destruct ccy as [f Hf]; simpl;
            now induction n as [|n IHn]; [apply idpath|]; rewrite IHn, <- (Hf n (S n) (idpath _)), id_left).
- abstract (intro p; apply subtypeEquality;
              [ intros f; apply impred; intro; apply hsD
              | now simpl; destruct p as [p H]; rewrite <- (H 0), id_left]).
Defined.

Definition omega_cocont_constant_functor : omega_cocont_functor C D :=
  tpair _ _ is_omega_cocont_constant_functor.

End constant_functor.

(** ** Functor composition preserves omega cocontinuity *)
Section functor_composite.

Context {C D E : precategory} (hsE : has_homsets E).

Lemma preserves_colimit_functor_composite (F : functor C D) (G : functor D E)
  {g : graph} (d : diagram g C) (L : C) (cc : cocone d L)
  (H1 : preserves_colimit F d L cc)
  (H2 : preserves_colimit G (mapdiagram F d) (F L) (mapcocone F _ cc)) :
  preserves_colimit (functor_composite F G) d L cc.
Proof.
intros HcL y ccy; simpl.
set (CC := mk_ColimCocone _ _ _ (H2 (H1 HcL))).
mkpair.
- mkpair.
  + apply (colimArrow CC), ccy.
  + abstract (simpl; intro v; apply (colimArrowCommutes CC)).
- abstract (simpl; intro t; apply subtypeEquality;
    [ intros f; apply impred; intro; apply hsE
    | simpl; apply (colimArrowUnique CC), (pr2 t) ]).
Defined.

Lemma is_cocont_functor_composite (F : functor C D) (G : functor D E)
  (HF : is_cocont F) (HG : is_cocont G) : is_cocont (functor_composite F G).
Proof.
intros g d L cc.
apply preserves_colimit_functor_composite; [ apply HF | apply HG ].
Defined.

Lemma is_omega_cocont_functor_composite (F : functor C D) (G : functor D E) :
  is_omega_cocont F -> is_omega_cocont G -> is_omega_cocont (functor_composite F G).
Proof.
intros hF hG c L cc.
apply preserves_colimit_functor_composite; [ apply hF | apply hG ].
Defined.

Definition omega_cocont_functor_composite
  (F : omega_cocont_functor C D) (G : omega_cocont_functor D E) :
  omega_cocont_functor C E := tpair _ _ (is_omega_cocont_functor_composite _ _ (pr2 F) (pr2 G)).

End functor_composite.

(** ** Functor iteration preserves (omega)-cocontinuity *)
Section iter_functor.

Lemma is_cocont_iter_functor {C : precategory} (hsC : has_homsets C)
  (F : functor C C) (hF : is_cocont F) n : is_cocont (iter_functor F n).
Proof.
induction n as [|n IH]; simpl.
- apply (is_cocont_functor_identity hsC).
- apply (is_cocont_functor_composite hsC _ _ IH hF).
Defined.

Lemma is_omega_cocont_iter_functor {C : precategory} (hsC : has_homsets C)
  (F : functor C C) (hF : is_omega_cocont F) n : is_omega_cocont (iter_functor F n).
Proof.
induction n as [|n IH]; simpl.
- apply (is_omega_cocont_functor_identity hsC).
- apply (is_omega_cocont_functor_composite hsC _ _ IH hF).
Defined.

Definition omega_cocont_iter_functor {C : precategory} (hsC : has_homsets C)
  (F : omega_cocont_functor C C) n : omega_cocont_functor C C :=
  tpair _ _ (is_omega_cocont_iter_functor hsC _ (pr2 F) n).

End iter_functor.

(** ** A pair of functors (F,G) : A * B -> C * D is omega cocontinuous if F and G are *)
Section pair_functor.

Context {A B C D : precategory} (F : functor A C) (G : functor B D)
        (hsA : has_homsets A) (hsB : has_homsets B) (hsC : has_homsets C) (hsD : has_homsets D).


Local Definition cocone_pr1_functor {g : graph} (cAB : diagram g (precategory_binproduct A B))
  (ab : A × B) (ccab : cocone cAB ab) :
  cocone (mapdiagram (pr1_functor A B) cAB) (ob1 ab).
Proof.
use mk_cocone.
- simpl; intro n; apply (mor1 (coconeIn ccab n)).
- abstract (simpl; intros m n e; now rewrite <- (coconeInCommutes ccab m n e)).
Defined.

Local Lemma isColimCocone_pr1_functor {g : graph} (cAB : diagram g (precategory_binproduct A B))
  (ab : A × B) (ccab : cocone cAB ab) (Hccab : isColimCocone cAB ab ccab) :
   isColimCocone (mapdiagram (pr1_functor A B) cAB) (ob1 ab)
     (mapcocone (pr1_functor A B) cAB ccab).
Proof.
intros x ccx.
transparent assert (HHH : (cocone cAB (x,, ob2 ab))).
{ use mk_cocone.
  - simpl; intro n; split;
      [ apply (pr1 ccx n) | apply (# (pr2_functor A B) (pr1 ccab n)) ].
  - abstract(simpl; intros m n e; rewrite (tppr (dmor cAB e)); apply pathsdirprod;
               [ apply (pr2 ccx m n e) | apply (maponpaths dirprod_pr2 ((pr2 ccab) m n e)) ]).
}
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2].
mkpair.
- apply (tpair _ x1).
  abstract (intro n; apply (maponpaths pr1 (p1 n))).
- intro t.
  transparent assert (X : (∑ x0, ∏ v, coconeIn ccab v · x0 =
                                 precatbinprodmor (pr1 ccx v) (pr2 (pr1 ccab v)))).
  { mkpair.
    - split; [ apply (pr1 t) | apply (identity _) ].
    - abstract (intro n; rewrite id_right; apply pathsdirprod;
                 [ apply (pr2 t) | apply idpath ]).
  }
  abstract (apply subtypeEquality; simpl;
            [ intro f; apply impred; intro; apply hsA
            | apply (maponpaths (fun x => pr1 (pr1 x)) (p2 X))]).
Defined.

Lemma is_cocont_pr1_functor : is_cocont (pr1_functor A B).
Proof.
now intros c L ccL M H; apply isColimCocone_pr1_functor.
Defined.

Local Definition cocone_pr2_functor {g : graph} (cAB : diagram g (precategory_binproduct A B))
  (ab : A × B) (ccab : cocone cAB ab) :
  cocone (mapdiagram (pr2_functor A B) cAB) (pr2 ab).
Proof.
use mk_cocone.
- simpl; intro n; apply (pr2 (coconeIn ccab n)).
- abstract (simpl; intros m n e; now rewrite <- (coconeInCommutes ccab m n e)).
Defined.

Local Lemma isColimCocone_pr2_functor {g : graph} (cAB : diagram g (precategory_binproduct A B))
  (ab : A × B) (ccab : cocone cAB ab) (Hccab : isColimCocone cAB ab ccab) :
   isColimCocone (mapdiagram (pr2_functor A B) cAB) (pr2 ab)
     (mapcocone (pr2_functor A B) cAB ccab).
Proof.
intros x ccx.
transparent assert (HHH : (cocone cAB (pr1 ab,, x))).
{ use mk_cocone.
  - simpl; intro n; split;
      [ apply (# (pr1_functor A B) (pr1 ccab n)) | apply (pr1 ccx n) ].
  - abstract (simpl; intros m n e; rewrite (tppr (dmor cAB e)); apply pathsdirprod;
                [ apply (maponpaths pr1 (pr2 ccab m n e)) | apply (pr2 ccx m n e) ]).
 }
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2].
mkpair.
- apply (tpair _ x2).
  abstract (intro n; apply (maponpaths dirprod_pr2 (p1 n))).
- intro t.
  transparent assert (X : (∑ x0, ∏ v, coconeIn ccab v · x0 =
                                 precatbinprodmor (pr1 (pr1 ccab v)) (pr1 ccx v))).
  { mkpair.
    - split; [ apply (identity _) | apply (pr1 t) ].
    - abstract (intro n; rewrite id_right; apply pathsdirprod;
                 [ apply idpath | apply (pr2 t) ]).
  }
  abstract (apply subtypeEquality; simpl;
              [ intro f; apply impred; intro; apply hsB
              | apply (maponpaths (fun x => dirprod_pr2 (pr1 x)) (p2 X)) ]).
Defined.

Lemma is_cocont_pr2_functor : is_cocont (pr2_functor A B).
Proof.
now intros c L ccL M H; apply isColimCocone_pr2_functor.
Defined.

Lemma isColimCocone_pair_functor {gr : graph}
  (HF : ∏ (d : diagram gr A) (c : A) (cc : cocone d c) (h : isColimCocone d c cc),
        isColimCocone _ _ (mapcocone F d cc))
  (HG : ∏ (d : diagram gr B) (c : B) (cc : cocone d c) (h : isColimCocone d c cc),
        isColimCocone _ _ (mapcocone G d cc)) :
  ∏ (d : diagram gr (precategory_binproduct A B)) (cd : A × B) (cc : cocone d cd),
  isColimCocone _ _ cc ->
  isColimCocone _ _ (mapcocone (pair_functor F G) d cc).
Proof.
intros cAB ml ccml Hccml xy ccxy.
transparent assert (cFAX : (cocone (mapdiagram F (mapdiagram (pr1_functor A B) cAB)) (pr1 xy))).
{ use mk_cocone.
  - intro n; apply (pr1 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr1 (pr2 ccxy m n e))).
}
transparent assert (cGBY : (cocone (mapdiagram G (mapdiagram (pr2_functor A B) cAB)) (pr2 xy))).
{ use mk_cocone.
  - intro n; apply (pr2 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr2 (pr2 ccxy m n e))).
}
destruct (HF _ _ _ (isColimCocone_pr1_functor cAB ml ccml Hccml) _ cFAX) as [[f hf1] hf2].
destruct (HG _ _ _ (isColimCocone_pr2_functor cAB ml ccml Hccml) _ cGBY) as [[g hg1] hg2].
simpl in *.
mkpair.
- apply (tpair _ (f,,g)).
  abstract (intro n; unfold precatbinprodmor, compose; simpl;
            now rewrite hf1, hg1, (tppr (coconeIn ccxy n))).
- abstract (intro t; apply subtypeEquality; simpl;
             [ intro x; apply impred; intro; apply isaset_dirprod; [ apply hsC | apply hsD ]
             | induction t as [[f1 f2] p]; simpl in *; apply pathsdirprod;
               [ apply (maponpaths pr1 (hf2 (f1,, (λ n, maponpaths pr1 (p n)))))
               | apply (maponpaths pr1 (hg2 (f2,, (λ n, maponpaths dirprod_pr2 (p n)))))]]).
Defined.

Lemma is_cocont_pair_functor (HF : is_cocont F) (HG : is_cocont G) :
  is_cocont (pair_functor F G).
Proof.
intros gr cAB ml ccml Hccml.
now apply isColimCocone_pair_functor; [apply HF|apply HG|].
Defined.

Lemma is_omega_cocont_pair_functor (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (pair_functor F G).
Proof.
now intros cAB ml ccml Hccml; apply isColimCocone_pair_functor.
Defined.

End pair_functor.

(** ** A functor F : A -> product_precategory I B is (omega-)cocontinuous if each F_i : A -> B_i is *)
Section functor_into_product_precategory.
(* NOTE: section below on [power_precategory] may be easily(?) generalised to [product_precategory]. *)
(* NOTE: binary analogue for this section. *)

Context {I : UU} {A : precategory} (hsA : has_homsets A)
  {B : I -> precategory} (hsB : forall i, has_homsets (B i)).

(* A cocone in the [product_precategory] is a colimit cocone if each of its components is.

Cf. the converse [isColimCocone_functor_into_power] below (currently only for special case of power,
not product), which seems to require some additional assumption (e.g. decidable equality on [I];
perhaps other conditions might also suffice. *)
(* NOTE: other lemmas in below on cocones in [power_precategory] may be able to be simplified using this. *)
Lemma isColimCocone_in_product_precategory
  {g : graph} (c : diagram g (product_precategory I B))
  (b : product_precategory I B) (cc : cocone c b)
  (M : ∏ i, isColimCocone _ _ (mapcocone (pr_functor I B i) _ cc))
  : isColimCocone c b cc.
Proof.
  intros b' cc'.
  apply iscontraprop1.
  - abstract (
    apply invproofirrelevance; intros f1 f2;
    apply subtypeEquality;
    [ intros f; apply impred_isaprop; intros v;
      apply has_homsets_product_precategory, hsB | ];
    apply funextsec; intros i;
    assert (MM := M i _ (mapcocone (pr_functor I B i) _ cc'));
    assert (H := proofirrelevance _ (isapropifcontr MM));
    refine (maponpaths pr1 (H (pr1 f1 i,,_) (pr1 f2 i,,_)));
      clear MM H; intros v ;
      [ exact (toforallpaths _ _ _ (pr2 f1 v) i) |
        exact (toforallpaths _ _ _ (pr2 f2 v) i) ]
      ) .
  - mkpair.
    + intros i.
      refine (pr1 (pr1 (M i _ (mapcocone (pr_functor I B i) _ cc')))).
    + abstract (
          intros v; apply funextsec; intros i;
          refine (pr2 (pr1 (M i _ (mapcocone (pr_functor I B i) _ cc'))) v)
        ).
Defined.

Lemma is_cocont_functor_into_product_precategory
  {F : functor A (product_precategory I B)}
  (HF : ∏ (i : I), is_cocont (functor_composite F (pr_functor I B i))) :
  is_cocont F.
Proof.
  intros gr cA a cc Hcc.
  apply isColimCocone_in_product_precategory.
  intros i.
  rewrite <- mapcocone_functor_composite; try apply hsB.
  now apply HF, Hcc.
Defined.

Lemma is_omega_cocont_functor_into_product_precategory
  {F : functor A (product_precategory I B)}
  (HF : ∏ (i : I), is_omega_cocont (functor_composite F (pr_functor I B i))) :
  is_omega_cocont F.
Proof.
  intros cA a cc Hcc.
  apply isColimCocone_in_product_precategory.
  intros i.
  rewrite <- mapcocone_functor_composite; try apply hsB.
  now apply HF, Hcc.
Defined.

End functor_into_product_precategory.

Section tuple_functor.

Context {I : UU} {A : precategory} {B : I -> precategory} (hsB : ∏ i, has_homsets (B i)).

Lemma is_cocont_tuple_functor {F : ∏ i, functor A (B i)}
  (HF : ∏ i, is_cocont (F i)) : is_cocont (tuple_functor F).
Proof.
  apply is_cocont_functor_into_product_precategory; try apply hsB.
  intro i; rewrite (pr_tuple_functor hsB); apply HF.
Defined.

Lemma is_omega_cocont_tuple_functor {F : ∏ i, functor A (B i)}
  (HF : ∏ i, is_omega_cocont (F i)) : is_omega_cocont (tuple_functor F).
Proof.
  apply is_omega_cocont_functor_into_product_precategory; try apply hsB.
  intro i; rewrite  (pr_tuple_functor hsB); apply HF.
Defined.

End tuple_functor.

(** ** A family of functor F^I : A^I -> B^I is omega cocontinuous if each F_i is *)
(** TODO: split out section [pr_functor], and then factor results on [family_functor] using that
together with [tuple_functor] (maybe after redefining [family_functor] using [tuple_functor]. *)
Section family_functor.

Context {I : UU} {A B : precategory} (hsA : has_homsets A) (hsB : has_homsets B).

(* The index set I needs decidable equality for pr_functor to be cocont *)
Hypothesis (HI : isdeceq I).

Local Definition ifI (i j : I) (a b : A) : A :=
  coprod_rect (λ _, A) (λ _,a) (λ _,b) (HI i j).

Local Lemma ifI_eq i x y : ifI i i x y = x.
Proof.
now unfold ifI; destruct (HI i i) as [p|p]; [|destruct (p (idpath _))].
Defined.

Local Lemma isColimCocone_pr_functor
  {g : graph} (c : diagram g (power_precategory I A))
  (L : power_precategory I A) (ccL : cocone c L)
  (M : isColimCocone c L ccL) : ∏ i,
  isColimCocone _ _ (mapcocone (pr_functor I (fun _ => A) i) c ccL).
Proof.
intros i x ccx; simpl in *.
transparent assert (HHH : (cocone c (fun j => ifI i j x (L j)))).
{ unfold ifI.
  use mk_cocone.
  - simpl; intros n j.
    destruct (HI i j) as [p|p].
    + apply (transportf (fun i => A ⟦ dob c n i, x ⟧) p (coconeIn ccx n)).
    + apply (# (pr_functor I (fun _ => A) j) (coconeIn ccL n)).
  - abstract (simpl; intros m n e;
      apply funextsec; intro j; unfold compose; simpl;
      destruct (HI i j);
        [ destruct p; apply (pr2 ccx m n e)
        | apply (toforallpaths _ _ _ (pr2 ccL m n e) j)]).
}
destruct (M _ HHH) as [[x1 p1] p2].
mkpair.
- apply (tpair _ (transportf _ (ifI_eq _ _ _) (x1 i))).
  abstract (intro n;
    rewrite <- idtoiso_postcompose, assoc;
    eapply pathscomp0;
      [eapply cancel_postcomposition, (toforallpaths _ _ _ (p1 n) i)|];
    unfold ifI, ifI_eq; simpl;
    destruct (HI i i); [|destruct (n0 (idpath _))];
    rewrite idtoiso_postcompose, idpath_transportf;
    assert (hp : p = idpath i); [apply (isasetifdeceq _ HI)|];
    now rewrite hp, idpath_transportf).
- intro t.
  transparent assert (X : (∑ x0, ∏ n, coconeIn ccL n · x0 = coconeIn HHH n)).
  { mkpair.
    - simpl; intro j; unfold ifI.
      destruct (HI i j).
      + apply (transportf (fun i => A ⟦ L i, x ⟧) p (pr1 t)).
      + apply identity.
    - abstract (intro n; apply funextsec; intro j; unfold ifI; destruct (HI i j);
          [ now destruct p; rewrite <- (pr2 t), !idpath_transportf
          | apply id_right ]).
  }
  apply subtypeEquality; simpl; [intro f; apply impred; intro; apply hsA|].
  set (H := toforallpaths _ _ _ (maponpaths pr1 (p2 X)) i); simpl in H.
  rewrite <- H; clear H; unfold ifI_eq, ifI.
  destruct (HI i i) as [p|p]; [|destruct (p (idpath _))].
  assert (hp : p = idpath i); [apply (isasetifdeceq _ HI)|].
  now rewrite hp, idpath_transportf.
Defined.

Lemma is_cocont_pr_functor (i : I) : is_cocont (pr_functor I (fun _ => A) i).
Proof.
now intros c L ccL M H; apply isColimCocone_pr_functor.
Defined.

Lemma isColimCocone_family_functor {gr : graph} (F : ∏ (i : I), functor A B)
  (HF : ∏ i (d : diagram gr A) (c : A) (cc : cocone d c) (h : isColimCocone d c cc),
        isColimCocone _ _ (mapcocone (F i) d cc)) :
  ∏ (d : diagram gr (product_precategory I (λ _, A))) (cd : I -> A) (cc : cocone d cd),
  isColimCocone _ _ cc ->
  isColimCocone _ _ (mapcocone (family_functor I F) d cc).
Proof.
intros cAB ml ccml Hccml xy ccxy; simpl in *.
transparent assert (cc : (∏ i, cocone (mapdiagram (F i) (mapdiagram (pr_functor I (λ _ : I, A) i) cAB)) (xy i))).
{ intro i; use mk_cocone.
  - intro n; simple refine (pr1 ccxy n _).
  - abstract (intros m n e; apply (toforallpaths _ _ _ (pr2 ccxy m n e) i)).
}
set (X i := HF i _ _ _ (isColimCocone_pr_functor _ _ _ Hccml i) (xy i) (cc i)).
mkpair.
- mkpair.
  + intro i; apply (pr1 (pr1 (X i))).
  + abstract (intro n; apply funextsec; intro j; apply (pr2 (pr1 (X j)) n)).
- abstract (intro t; apply subtypeEquality; simpl;
             [ intro x; apply impred; intro; apply impred_isaset; intro i; apply hsB
             | destruct t as [f1 f2]; simpl in *;  apply funextsec; intro i;
               transparent assert (H : (∑ x : B ⟦ (F i) (ml i), xy i ⟧,
                                       ∏ n, # (F i) (coconeIn ccml n i) · x =
                                       coconeIn ccxy n i));
                [apply (tpair _ (f1 i)); intro n; apply (toforallpaths _ _ _ (f2 n) i)|];
               apply (maponpaths pr1 (pr2 (X i) H))]).
Defined.

Lemma is_cocont_family_functor
  {F : ∏ (i : I), functor A B} (HF : ∏ (i : I), is_cocont (F i)) :
  is_cocont (family_functor I F).
Proof.
intros gr cAB ml ccml Hccml.
apply isColimCocone_family_functor; trivial; intro i; apply HF.
Defined.

Lemma is_omega_cocont_family_functor
  {F : ∏ (i : I), functor A B} (HF : ∏ (i : I), is_omega_cocont (F i)) :
  is_omega_cocont (family_functor I F).
Proof.
now intros cAB ml ccml Hccml; apply isColimCocone_family_functor.
Defined.

End family_functor.


(** ** The bindelta functor C -> C^2 mapping x to (x,x) is omega cocontinuous *)
Section bindelta_functor.

Context {C : precategory} (PC : BinProducts C) (hsC : has_homsets C).

Lemma is_cocont_bindelta_functor : is_cocont (bindelta_functor C).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_bindelta_functor PC) hsC).
abstract (apply (has_homsets_precategory_binproduct _ _ hsC hsC)).
Defined.

Lemma is_omega_cocont_bindelta_functor : is_omega_cocont (bindelta_functor C).
Proof.
now intros c L ccL; apply is_cocont_bindelta_functor.
Defined.

End bindelta_functor.

(** ** The generalized delta functor C -> C^I is omega cocontinuous *)
Section delta_functor.
(* TODO: factor this using [tuple_functor] results above, after redefining [delta_functor] in terms of [tuple_functor]. *)

Context {I : UU} {C : precategory} (PC : Products I C) (hsC : has_homsets C).

Lemma is_cocont_delta_functor : is_cocont (delta_functor I C).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_delta_functor _ PC) hsC).
abstract (apply (has_homsets_power_precategory _ _ hsC)).
Defined.

Lemma is_omega_cocont_delta_functor :
  is_omega_cocont (delta_functor I C).
Proof.
now intros c L ccL; apply is_cocont_delta_functor.
Defined.

End delta_functor.

(** ** The functor "+ : C^2 -> C" is cocontinuous *)
Section bincoprod_functor.

Context {C : precategory} (PC : BinCoproducts C) (hsC : has_homsets C).

Lemma is_cocont_bincoproduct_functor : is_cocont (bincoproduct_functor PC).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_bincoproduct_functor PC)).
- abstract (apply has_homsets_precategory_binproduct; apply hsC).
- abstract (apply hsC).
Defined.

Lemma is_omega_cocont_bincoproduct_functor :
  is_omega_cocont (bincoproduct_functor PC).
Proof.
now intros c L ccL; apply is_cocont_bincoproduct_functor.
Defined.

End bincoprod_functor.

(** ** The functor "+ : C^I -> C" is cocontinuous *)
Section coprod_functor.

Context {I : UU} {C : precategory} (PC : Coproducts I C) (hsC : has_homsets C).

Lemma is_cocont_coproduct_functor :
  is_cocont (coproduct_functor _ PC).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_coproduct_functor _ PC)).
- abstract (apply has_homsets_power_precategory; apply hsC).
- abstract (apply hsC).
Defined.

Lemma is_omega_cocont_coproduct_functor :
  is_omega_cocont (coproduct_functor _ PC).
Proof.
now intros c L ccL; apply is_cocont_coproduct_functor.
Defined.

End coprod_functor.

(** ** Binary coproduct of functors: F + G : C -> D is omega cocontinuous *)
Section BinCoproduct_of_functors.

Context {C D : precategory} (HD : BinCoproducts D) (hsD : has_homsets D).

Lemma is_cocont_BinCoproduct_of_functors_alt {F G : functor C D}
  (HF : is_cocont F) (HG : is_cocont G) :
  is_cocont (BinCoproduct_of_functors_alt hsD HD F G).
Proof.
apply (is_cocont_functor_composite hsD).
- apply is_cocont_tuple_functor; [intros b; apply hsD|].
  induction i; assumption.
- apply is_cocont_coproduct_functor, hsD.
Defined.

Lemma is_omega_cocont_BinCoproduct_of_functors_alt {F G : functor C D}
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinCoproduct_of_functors_alt hsD HD F G).
Proof.
apply (is_omega_cocont_functor_composite hsD).
- apply is_omega_cocont_tuple_functor; [intros b; apply hsD|].
  induction i; assumption.
- apply is_omega_cocont_coproduct_functor, hsD.
Defined.

Definition omega_cocont_BinCoproduct_of_functors_alt (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinCoproduct_of_functors_alt (pr2 F) (pr2 G)).

Lemma is_cocont_BinCoproduct_of_functors (F G : functor C D)
  (HF : is_cocont F) (HG : is_cocont G) :
  is_cocont (BinCoproduct_of_functors _ _ HD F G).
Proof.
exact (transportf _
         (BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors _ _ _ _ F G)
         (is_cocont_BinCoproduct_of_functors_alt HF HG)).
Defined.

Lemma is_omega_cocont_BinCoproduct_of_functors (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinCoproduct_of_functors _ _ HD F G).
Proof.
exact (transportf _
         (BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors _ _ _ _ F G)
         (is_omega_cocont_BinCoproduct_of_functors_alt HF HG)).
Defined.

Definition omega_cocont_BinCoproduct_of_functors
 (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinCoproduct_of_functors _ _ (pr2 F) (pr2 G)).

(* Keep these as they have better computational behavior than the one for _alt above *)
Lemma is_cocont_BinCoproduct_of_functors_alt2 {hsC : has_homsets C}
  (PC : BinProducts C) (F G : functor C D)
  (HF : is_cocont F) (HG : is_cocont G) :
  is_cocont (BinCoproduct_of_functors_alt2 HD F G).
Proof.
apply (is_cocont_functor_composite hsD).
  apply (is_cocont_bindelta_functor PC hsC).
apply (is_cocont_functor_composite hsD).
  apply (is_cocont_pair_functor _ _ hsC hsC hsD hsD HF HG).
apply (is_cocont_bincoproduct_functor _ hsD).
Defined.

Lemma is_omega_cocont_BinCoproduct_of_functors_alt2 (hsC : has_homsets C)
  (PC : BinProducts C) (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinCoproduct_of_functors_alt2 HD F G).
Proof.
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_bindelta_functor PC hsC).
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_pair_functor _ _ hsC hsC hsD hsD HF HG).
apply (is_omega_cocont_bincoproduct_functor _ hsD).
Defined.

Definition omega_cocont_BinCoproduct_of_functors_alt2 (hsC : has_homsets C)
  (PC : BinProducts C) (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinCoproduct_of_functors_alt2 hsC PC _ _ (pr2 F) (pr2 G)).

End BinCoproduct_of_functors.

(** ** Coproduct of families of functors: + F_i : C -> D is omega cocontinuous *)
Section coproduct_of_functors.

Context {I : UU} {C D : precategory} (HD : Coproducts I D) (hsD : has_homsets D).

Lemma is_cocont_coproduct_of_functors
  {F : ∏ (i : I), functor C D} (HF : ∏ i, is_cocont (F i)) :
  is_cocont (coproduct_of_functors I _ _ HD F).
Proof.
  refine (transportf _
        (coproduct_of_functors_alt_eq_coproduct_of_functors _ _ _ _ hsD F)
        _).
  apply is_cocont_functor_composite; try apply hsD.
  - apply is_cocont_tuple_functor; try (intro; apply hsD).
    apply HF.
  - apply is_cocont_coproduct_functor; try apply hsD.
Defined.

Lemma is_omega_cocont_coproduct_of_functors
  {F : ∏ (i : I), functor C D} (HF : ∏ i, is_omega_cocont (F i)) :
  is_omega_cocont (coproduct_of_functors I _ _ HD F).
Proof.
  refine (transportf _
        (coproduct_of_functors_alt_eq_coproduct_of_functors _ _ _ _ hsD F)
        _).
  apply is_omega_cocont_functor_composite; try apply hsD.
  - apply is_omega_cocont_tuple_functor; try (intro; apply hsD).
    apply HF.
  - apply is_omega_cocont_coproduct_functor; try apply hsD.
Defined.

Definition omega_cocont_coproduct_of_functors
  (F : ∏ i, omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_coproduct_of_functors (fun i => pr2 (F i))).

End coproduct_of_functors.

(** ** Constant product functors: C -> C, x |-> a * x  and  x |-> x * a are cocontinuous *)
Section constprod_functors.

Context {C : precategory} (PC : BinProducts C) (hsC : has_homsets C) (hE : has_exponentials PC).

Lemma is_cocont_constprod_functor1 (x : C) : is_cocont (constprod_functor1 PC x).
Proof.
exact (left_adjoint_cocont _ (hE _) hsC hsC).
Defined.

Lemma is_omega_cocont_constprod_functor1 (x : C) : is_omega_cocont (constprod_functor1 PC x).
Proof.
now intros c L ccL; apply is_cocont_constprod_functor1.
Defined.

Definition omega_cocont_constprod_functor1 (x : C) :
  omega_cocont_functor C C := tpair _ _ (is_omega_cocont_constprod_functor1 x).

Lemma is_cocont_constprod_functor2 (x : C) : is_cocont (constprod_functor2 PC x).
Proof.
apply left_adjoint_cocont; try apply hsC.
apply (is_left_adjoint_constprod_functor2 PC hsC), hE.
Defined.

Lemma is_omega_cocont_constprod_functor2 (x : C) : is_omega_cocont (constprod_functor2 PC x).
Proof.
now intros c L ccL; apply is_cocont_constprod_functor2.
Defined.

Definition omega_cocont_constprod_functor2 (x : C) :
  omega_cocont_functor C C := tpair _ _ (is_omega_cocont_constprod_functor2 x).

End constprod_functors.

(** ** The functor "* : C^2 -> C" is omega cocontinuous *)
Section binprod_functor.

Context {C : precategory} (PC : BinProducts C) (hsC : has_homsets C).

(* This hypothesis follow directly if C has exponentials *)
Variable omega_cocont_constprod_functor1 :
  ∏ x : C, is_omega_cocont (constprod_functor1 PC x).

Let omega_cocont_constprod_functor2 :
  ∏ x : C, is_omega_cocont (constprod_functor2 PC x).
Proof.
now intro x; apply (is_omega_cocont_iso hsC (flip_iso PC hsC x)).
Defined.

Local Definition fun_lt (cAB : chain (precategory_binproduct C C)) :
  ∏ i j, i < j ->
              C ⟦ BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))),
                  BinProductObject C (PC (ob1 (dob cAB j)) (ob2 (dob cAB j))) ⟧.
Proof.
intros i j hij.
apply (BinProductOfArrows _ _ _ (mor1 (chain_mor cAB hij)) (identity _)).
Defined.

Local Definition fun_gt (cAB : chain (precategory_binproduct C C)) :
  ∏ i j, i > j ->
              C ⟦ BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))),
                  BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB i))) ⟧.
Proof.
intros i j hij.
apply (BinProductOfArrows _ _ _ (identity _) (mor2 (chain_mor cAB hij))).
Defined.

(* The map to K from the "grid" *)
Local Definition map_to_K (cAB : chain (precategory_binproduct C C)) (K : C)
  (ccK : cocone (mapchain (binproduct_functor PC) cAB) K) i j :
  C⟦BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))), K⟧.
Proof.
destruct (natlthorgeh i j).
- apply (fun_lt cAB _ _ h · coconeIn ccK j).
- destruct (natgehchoice _ _ h) as [H|H].
  * apply (fun_gt cAB _ _ H · coconeIn ccK i).
  * destruct H; apply (coconeIn ccK i).
Defined.

Local Lemma map_to_K_commutes (cAB : chain (precategory_binproduct C C)) (K : C)
  (ccK : cocone (mapchain (binproduct_functor PC) cAB) K)
  i j k (e : edge j k) :
   BinProduct_of_functors_mor C C PC (constant_functor C C (pr1 (pr1 cAB i)))
     (functor_identity C) (pr2 (dob cAB j)) (pr2 (dob cAB k))
     (mor2 (dmor cAB e)) · map_to_K cAB K ccK i k =
   map_to_K cAB K ccK i j.
Proof.
destruct e; simpl.
unfold BinProduct_of_functors_mor, map_to_K.
destruct (natlthorgeh i j) as [h|h].
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * rewrite assoc, <- (coconeInCommutes ccK j (S j) (idpath _)), assoc; simpl.
    apply cancel_postcomposition; unfold fun_lt.
    rewrite BinProductOfArrows_comp, id_left.
    eapply pathscomp0; [apply BinProductOfArrows_comp|].
    rewrite id_right.
    apply BinProductOfArrows_eq; trivial; rewrite id_left; simpl.
    destruct (natlehchoice4 i j h0) as [h1|h1].
    + apply cancel_postcomposition, maponpaths, maponpaths, isasetbool.
    + destruct h1; destruct (isirreflnatlth _ h).
  * destruct (isirreflnatlth _ (natlthlehtrans _ _ _ (natlthtolths _ _ h) h0)).
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natlthchoice2 _ _ h1) as [h2|h2].
      { destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)). }
      { destruct h2; destruct (isirreflnatlth _ h0). }
    + destruct h1; simpl.
      rewrite <- (coconeInCommutes ccK i (S i) (idpath _)), assoc.
      eapply pathscomp0; [apply cancel_postcomposition, BinProductOfArrows_comp|].
      rewrite id_left, id_right.
      apply cancel_postcomposition, BinProductOfArrows_eq; trivial.
      simpl; destruct (natlehchoice4 i i h0) as [h1|h1]; [destruct (isirreflnatlth _ h1)|].
      apply maponpaths, maponpaths, isasetnat.
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natgehchoice i (S j) h0) as [h2|h2].
      { unfold fun_gt; rewrite assoc.
        eapply pathscomp0; [eapply cancel_postcomposition, BinProductOfArrows_comp|].
        rewrite id_right.
        apply cancel_postcomposition, BinProductOfArrows_eq; trivial.
        now rewrite <- (chain_mor_right h1 h2). }
      { destruct h; unfold fun_gt; simpl.
        generalize h1; clear h1.
        rewrite h2; intro h1.
        apply cancel_postcomposition.
        apply BinProductOfArrows_eq; trivial; simpl.
        destruct (natlehchoice4 j j h1); [destruct (isirreflnatlth _ h)|].
        apply maponpaths, maponpaths, isasetnat. }
    + destruct h1; destruct (negnatgehnsn _ h0).
Qed.

(* The cocone over K from the A_i * B chain *)
Local Definition ccAiB_K (cAB : chain (precategory_binproduct C C)) (K : C)
  (ccK : cocone (mapchain (binproduct_functor PC) cAB) K) i :
  cocone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i)))
         (mapchain (pr2_functor C C) cAB)) K.
Proof.
use mk_cocone.
+ intro j; apply (map_to_K cAB K ccK i j).
+ simpl; intros j k e; apply map_to_K_commutes.
Defined.

Section omega_cocont_binproduct.

Context {cAB : chain (precategory_binproduct C C)} {LM : C × C}
        {ccLM : cocone cAB LM} (HccLM : isColimCocone cAB LM ccLM)
        {K : C} (ccK : cocone (mapchain (binproduct_functor PC) cAB) K).

Let L := pr1 LM : C.
Let M := pr2 LM : (λ _ : C, C) (pr1 LM).
Let cA := mapchain (pr1_functor C C) cAB : chain C.
Let cB := mapchain (pr2_functor C C) cAB : chain C.
Let HA := isColimCocone_pr1_functor hsC _ _ _ HccLM
  : isColimCocone cA L (cocone_pr1_functor cAB LM ccLM).
Let HB := isColimCocone_pr2_functor hsC _ _ _ HccLM
  : isColimCocone cB M (cocone_pr2_functor cAB LM ccLM).

(* Form the colimiting cocones of "A_i * B_0 -> A_i * B_1 -> ..." *)
Let HAiB := λ i, omega_cocont_constprod_functor1 (pr1 (pr1 cAB i)) _ _ _ HB.

(* Turn HAiB into a ColimCocone: *)
Let CCAiB := fun i => mk_ColimCocone _ _ _ (HAiB i).

(* Define the HAiM ColimCocone: *)
Let HAiM := mk_ColimCocone _ _ _ (omega_cocont_constprod_functor2 M _ _ _ HA).

Let ccAiB_K := fun i => ccAiB_K _ _ ccK i.

(* The f which is used in colimOfArrows *)
Local Definition f i j : C
   ⟦ BinProduct_of_functors_ob C C PC (constant_functor C C (pr1 (dob cAB i)))
       (functor_identity C) (pr2 (dob cAB j)),
     BinProduct_of_functors_ob C C PC (constant_functor C C (pr1 (dob cAB (S i))))
       (functor_identity C) (pr2 (dob cAB j)) ⟧.
Proof.
  apply BinProductOfArrows; [apply (dmor cAB (idpath _)) | apply identity ].
Defined.

Local Lemma fNat : ∏ i u v (e : edge u v),
   dmor (mapchain (constprod_functor1 PC _) cB) e · f i v =
   f i u · dmor (mapchain (constprod_functor1 PC _) cB) e.
Proof.
  intros i j k e; destruct e; simpl.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  eapply pathscomp0; [|eapply pathsinv0; apply BinProductOfArrows_comp].
  now rewrite !id_left, !id_right.
Qed.

(* Define the chain A_i * M *)
Local Definition AiM_chain : chain C.
Proof.
  mkpair.
  - intro i; apply (colim (CCAiB i)).
  - intros i j e; destruct e.
    apply (colimOfArrows (CCAiB i) (CCAiB (S i)) (f i) (fNat i)).
Defined.

Local Lemma AiM_chain_eq : ∏ i, dmor AiM_chain (idpath (S i)) =
                       dmor (mapchain (constprod_functor2 PC M) cA) (idpath _).
Proof.
  intro i; simpl; unfold colimOfArrows, BinProduct_of_functors_mor; simpl.
  apply pathsinv0, colimArrowUnique.
  simpl; intro j.
  unfold colimIn; simpl; unfold BinProduct_of_functors_mor, f; simpl.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  apply pathsinv0.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  now rewrite !id_left, !id_right.
Qed.

(* Define a cocone over K from the A_i * M chain *)
Local Lemma ccAiM_K_subproof : ∏ u v (e : edge u v),
   dmor (mapdiagram (constprod_functor2 PC M) cA) e ·
   colimArrow (CCAiB v) K (ccAiB_K v) = colimArrow (CCAiB u) K (ccAiB_K u).
Proof.
  intros i j e; destruct e; simpl.
  generalize (AiM_chain_eq i); simpl; intro H; rewrite <- H; clear H; simpl.
  eapply pathscomp0.
  apply (precompWithColimOfArrows _ _ (CCAiB i) (CCAiB (S i)) _ _ K (ccAiB_K (S i))).
  apply (colimArrowUnique (CCAiB i) K (ccAiB_K i)).
  simpl; intros j.
  eapply pathscomp0; [apply (colimArrowCommutes (CCAiB i) K)|]; simpl.
  unfold map_to_K.
  destruct (natlthorgeh (S i) j).
  + destruct (natlthorgeh i j).
    * rewrite assoc; apply cancel_postcomposition.
      unfold f, fun_lt; simpl.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      now rewrite id_right, <- (chain_mor_right h0 h).
    * destruct (isasymmnatgth _ _ h h0).
  + destruct (natgehchoice (S i) j h).
    * destruct h.
      { destruct (natlthorgeh i j).
        - destruct (natlthchoice2 _ _ h) as [h2|h2].
          + destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)).
          + destruct h2; destruct (isirreflnatlth _ h0).
        - destruct (natgehchoice i j h).
          + destruct h.
            rewrite <- (coconeInCommutes ccK i _ (idpath _)); simpl.
            rewrite !assoc; apply cancel_postcomposition.
            unfold f, fun_gt.
            rewrite BinProductOfArrows_comp.
            eapply pathscomp0; [apply BinProductOfArrows_comp|].
            now rewrite !id_left, !id_right, <- (chain_mor_left h1 h0).
          + destruct p.
            rewrite <- (coconeInCommutes ccK i _ (idpath _)), assoc.
            apply cancel_postcomposition.
            unfold f, fun_gt.
            eapply pathscomp0; [apply BinProductOfArrows_comp|].
            rewrite id_left, id_right.
            apply BinProductOfArrows_eq; trivial; simpl.
            destruct (natlehchoice4 i i h0); [destruct (isirreflnatlth _ h1)|].
            apply maponpaths, maponpaths, isasetnat.
       }
    * destruct p, h.
      destruct (natlthorgeh i (S i)); [|destruct (negnatgehnsn _ h)].
      apply cancel_postcomposition; unfold f, fun_lt.
      apply BinProductOfArrows_eq; trivial; simpl.
      destruct (natlehchoice4 i i h); [destruct (isirreflnatlth _ h0)|].
      assert (H : idpath (S i) = maponpaths S p). apply isasetnat.
      now rewrite H.
Qed.

Local Definition ccAiM_K := mk_cocone _ ccAiM_K_subproof.

Local Lemma is_cocone_morphism :
 ∏ v : nat,
   BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) ·
   colimArrow HAiM K ccAiM_K = coconeIn ccK v.
Proof.
  intro i.
  generalize (colimArrowCommutes HAiM K ccAiM_K i).
  assert (H : coconeIn ccAiM_K i = colimArrow (CCAiB i) K (ccAiB_K i)).
  { apply idpath. }
  rewrite H; intros HH.
  generalize (colimArrowCommutes (CCAiB i) K (ccAiB_K i) i).
  rewrite <- HH; simpl; unfold map_to_K.
  destruct (natlthorgeh i i); [destruct (isirreflnatlth _ h)|].
  destruct (natgehchoice i i h); [destruct (isirreflnatgth _ h0)|].
  simpl; destruct h, p.
  intros HHH.
  rewrite <- HHH, assoc.
  apply cancel_postcomposition.
  unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
  apply pathsinv0.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  now rewrite id_left, id_right.
Qed.

Local Lemma is_unique_cocone_morphism :
 ∏ t : ∑ x : C ⟦ BinProductObject C (PC L M), K ⟧,
       ∏ v : nat,
       BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
         (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) · x =
       coconeIn ccK v, t = colimArrow HAiM K ccAiM_K,, is_cocone_morphism.
Proof.
  intro t.
  apply subtypeEquality; simpl.
  + intro; apply impred; intros; apply hsC.
  + apply (colimArrowUnique HAiM K ccAiM_K).
    induction t as [t p]; simpl; intro i.
    apply (colimArrowUnique (CCAiB i) K (ccAiB_K i)).
    simpl; intros j; unfold map_to_K.
    induction (natlthorgeh i j) as [h|h].
    * rewrite <- (p j); unfold fun_lt.
      rewrite !assoc.
      apply cancel_postcomposition.
      unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      apply pathsinv0.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      rewrite !id_left, id_right.
      apply BinProductOfArrows_eq; trivial.
      apply (maponpaths pr1 (chain_mor_coconeIn cAB LM ccLM i j h)).
    * destruct (natgehchoice i j h).
      { unfold fun_gt; rewrite <- (p i), !assoc.
        apply cancel_postcomposition.
        unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        apply pathsinv0.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        now rewrite !id_left, id_right, <- (chain_mor_coconeIn cAB LM ccLM _ _ h0). }
      { destruct p0.
        rewrite <- (p i), assoc.
        apply cancel_postcomposition.
        unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        now rewrite id_left, id_right. }
Qed.

Local Definition isColimProductOfColims :  ∃! x : C ⟦ BinProductObject C (PC L M), K ⟧,
   ∏ v : nat,
   BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) · x =
   coconeIn ccK v.
Proof.
mkpair.
- mkpair.
  + apply (colimArrow HAiM K ccAiM_K).
  + apply is_cocone_morphism.
- apply is_unique_cocone_morphism.
Defined.

End omega_cocont_binproduct.

Lemma is_omega_cocont_binproduct_functor : is_omega_cocont (binproduct_functor PC).
Proof.
intros cAB LM ccLM HccLM K ccK; simpl in *.
apply isColimProductOfColims, HccLM.
Defined.

End binprod_functor.

(** ** Binary product of functors: F * G : C -> D is omega cocontinuous *)
Section BinProduct_of_functors.

Context {C D : precategory} (PC : BinProducts C) (PD : BinProducts D)
        (hsC : has_homsets C) (hsD : has_homsets D).

Variable omega_cocont_constprod_functor1 :
  ∏ x : D, is_omega_cocont (constprod_functor1 PD x).

Lemma is_omega_cocont_BinProduct_of_functors_alt (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinProduct_of_functors_alt PD F G).
Proof.
apply (is_omega_cocont_functor_composite hsD).
- apply (is_omega_cocont_bindelta_functor PC hsC).
- apply (is_omega_cocont_functor_composite hsD).
  + apply (is_omega_cocont_pair_functor _ _ hsC hsC hsD hsD HF HG).
  + now apply (is_omega_cocont_binproduct_functor _ hsD).
Defined.

Definition omega_cocont_BinProduct_of_functors_alt (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinProduct_of_functors_alt _ _ (pr2 F) (pr2 G)).

Lemma is_omega_cocont_BinProduct_of_functors (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinProduct_of_functors _ _ PD F G).
Proof.
exact (transportf _
        (BinProduct_of_functors_alt_eq_BinProduct_of_functors C D PD hsD F G)
        (is_omega_cocont_BinProduct_of_functors_alt _ _ HF HG)).
Defined.

Definition omega_cocont_BinProduct_of_functors (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinProduct_of_functors _ _ (pr2 F) (pr2 G)).

End BinProduct_of_functors.

(** ** Direct proof that the precomposition functor is cocontinuous *)
Section pre_composition_functor.

Context {A B C : precategory} (F : functor A B) (hsB : has_homsets B) (hsC : has_homsets C).
(* Context (CC : Colims C). *) (* This is too strong *)

Lemma preserves_colimit_pre_composition_functor {g : graph}
  (d : diagram g [B,C,hsC]) (G : [B,C,hsC])
  (ccG : cocone d G) (H : ∏ b, ColimCocone (diagram_pointwise hsC d b)) :
  preserves_colimit (pre_composition_functor A B C hsB hsC F) d G ccG.
Proof.
intros HccG.
apply pointwise_Colim_is_isColimFunctor; intro a.
now apply (isColimFunctor_is_pointwise_Colim _ _ H _ _ HccG).
Defined.

(* Lemma is_cocont_pre_composition_functor *)
(*   (H : ∏ (g : graph) (d : diagram g [B,C,hsC]) (b : B), *)
(*        ColimCocone (diagram_pointwise hsC d b)) : *)
(*   is_cocont (pre_composition_functor _ _ _ hsB hsC F). *)
(* Proof. *)
(* now intros g d G ccG; apply preserves_colimit_pre_composition_functor. *)
(* Defined. *)

Lemma is_omega_cocont_pre_composition_functor
  (H : Colims_of_shape nat_graph C) :
  is_omega_cocont (pre_composition_functor _ _ _ hsB hsC F).
Proof.
now intros c L ccL; apply preserves_colimit_pre_composition_functor.
Defined.

Definition omega_cocont_pre_composition_functor
  (H : Colims_of_shape nat_graph C) :
  omega_cocont_functor [B, C, hsC] [A, C, hsC] :=
  tpair _ _ (is_omega_cocont_pre_composition_functor H).

End pre_composition_functor.

(** ** Precomposition functor is cocontinuous using construction of right Kan extensions *)
Section pre_composition_functor_kan.

Context {A B C : precategory} (F : functor A B) (hsB : has_homsets B) (hsC : has_homsets C).
Context (LC : Lims C).

Lemma is_cocont_pre_composition_functor_kan :
  is_cocont (pre_composition_functor _ _ _ hsB hsC F).
Proof.
apply left_adjoint_cocont; try apply functor_category_has_homsets.
apply (RightKanExtension_from_limits _ _ _ LC).
Qed.

Lemma is_omega_cocont_pre_composition_functor_kan :
  is_omega_cocont (pre_composition_functor _ _ _ hsB hsC F).
Proof.
now intros c L ccL; apply is_cocont_pre_composition_functor_kan.
Defined.

Definition omega_cocont_pre_composition_functor_kan :
  omega_cocont_functor [B, C, hsC] [A, C, hsC] :=
  tpair _ _ is_omega_cocont_pre_composition_functor_kan.

End pre_composition_functor_kan.

Section post_composition_functor.

Context {C D E : precategory} (hsD : has_homsets D) (hsE : has_homsets E).
Context (F : functor D E) (HF : is_left_adjoint F).

Lemma is_cocont_post_composition_functor :
  is_cocont (post_composition_functor C D E hsD hsE F).
Proof.
apply left_adjoint_cocont; try apply functor_category_has_homsets.
apply (is_left_adjoint_post_composition_functor _ _ _ HF).
Defined.

Lemma is_omega_cocont_post_composition_functor :
  is_omega_cocont (post_composition_functor C D E hsD hsE F).
Proof.
now intros c L ccL; apply is_cocont_post_composition_functor.
Defined.

End post_composition_functor.

(** * Swapping of functor category arguments *)
Section functor_swap.

Lemma is_cocont_functor_cat_swap (C D : precategory) (E : category) :
  is_cocont (functor_cat_swap C D E).
Proof.
apply left_adjoint_cocont; try apply homset_property.
apply is_left_adjoint_functor_cat_swap.
Defined.

Lemma is_omega_cocont_functor_cat_swap (C D : precategory) (E : category) :
  is_omega_cocont (functor_cat_swap C D E).
Proof.
intros d L ccL HccL.
apply (is_cocont_functor_cat_swap _ _ _ _ d L ccL HccL).
Defined.

End functor_swap.

(** * The forgetful functor from Set/X to Set preserves colimits *)
Section cocont_slicecat_to_cat_HSET.

Local Notation "HSET / X" := (slice_precat HSET X has_homsets_HSET) (only parsing).

Lemma preserves_colimit_slicecat_to_cat_HSET (X : HSET)
  (g : graph) (d : diagram g (HSET / X)) (L : HSET / X) (ccL : cocone d L) :
  preserves_colimit (slicecat_to_cat has_homsets_HSET X) d L ccL.
Proof.
apply left_adjoint_preserves_colimit.
- apply is_left_adjoint_slicecat_to_cat_HSET.
- apply has_homsets_slice_precat.
- apply has_homsets_HSET.
Defined.

Lemma is_cocont_slicecat_to_cat_HSET (X : HSET) :
  is_cocont (slicecat_to_cat has_homsets_HSET X).
Proof.
intros g d L cc.
now apply preserves_colimit_slicecat_to_cat_HSET.
Defined.

Lemma is_omega_cocont_slicecat_to_cat (X : HSET) :
  is_omega_cocont (slicecat_to_cat has_homsets_HSET X).
Proof.
intros d L cc.
now apply preserves_colimit_slicecat_to_cat_HSET.
Defined.

(** Direct proof that the forgetful functor Set/X to Set preserves colimits *)
Lemma preserves_colimit_slicecat_to_cat_HSET_direct (X : HSET)
  (g : graph) (d : diagram g (HSET / X)) (L : HSET / X) (ccL : cocone d L) :
  preserves_colimit (slicecat_to_cat has_homsets_HSET X) d L ccL.
Proof.
intros HccL y ccy.
set (CC := mk_ColimCocone _ _ _ HccL).
transparent assert (c : (HSET / X)).
{ mkpair.
  - exists (∑ (x : pr1 X), pr1 y).
    abstract (apply isaset_total2; intros; apply setproperty).
  - apply pr1.
}
transparent assert (cc : (cocone d c)).
{ use mk_cocone.
  - intros n.
    mkpair; simpl.
    + intros z.
      mkpair.
      * exact (pr2 L (pr1 (coconeIn ccL n) z)).
      * apply (coconeIn ccy n z).
    + abstract (now apply funextsec; intro z;
                apply (toforallpaths _ _ _ (pr2 (coconeIn ccL n)) z)).
  - abstract (intros m n e; apply eq_mor_slicecat, funextsec; intro z;
    use total2_paths_f;
      [ apply (maponpaths _ (toforallpaths _ _ _
                 (maponpaths pr1 (coconeInCommutes ccL m n e)) z))|];
    cbn in *; induction (maponpaths pr1 _);
    simpl;
    now rewrite idpath_transportf, <- (coconeInCommutes ccy m n e)).
}
use unique_exists.
- intros l; apply (pr2 (pr1 (colimArrow CC c cc) l)).
- simpl; intro n.
  apply funextsec; intro x; cbn.
  now etrans; [apply maponpaths,
                 (toforallpaths _ _ _ (maponpaths pr1 (colimArrowCommutes CC c cc n)) x)|].
- intros z; apply impred_isaprop; intro n; apply setproperty.
- simpl; intros f Hf.
apply funextsec; intro l.
transparent assert (k : (HSET/X⟦colim CC,c⟧)).
{ mkpair.
  - intros l'.
    exists (pr2 L l').
    apply (f l').
  - abstract (now apply funextsec).
}
assert (Hk : (∏ n, colimIn CC n · k = coconeIn cc n)).
{ intros n.
  apply subtypeEquality; [intros x; apply setproperty|].
  apply funextsec; intro z.
  use total2_paths_f; [apply idpath|].
  now rewrite idpath_transportf; cbn; rewrite <- (toforallpaths _ _ _ (Hf n) z).
}
apply (maponpaths dirprod_pr2
         (toforallpaths _ _ _ (maponpaths pr1 (colimArrowUnique CC c cc k Hk)) l)).
Defined.

End cocont_slicecat_to_cat_HSET.
End cocont_functors.

(** Specialized notations for HSET *)
Delimit Scope cocont_functor_hset_scope with CS.

Notation "' x" := (omega_cocont_constant_functor has_homsets_HSET x)
                    (at level 10) : cocont_functor_hset_scope.

Notation "'Id'" := (omega_cocont_functor_identity has_homsets_HSET) :
                     cocont_functor_hset_scope.

Notation "F * G" :=
  (omega_cocont_BinProduct_of_functors_alt BinProductsHSET _
     has_homsets_HSET has_homsets_HSET
     (is_omega_cocont_constprod_functor1 _ has_homsets_HSET has_exponentials_HSET)
     F G) : cocont_functor_hset_scope.

Notation "F + G" :=
  (omega_cocont_BinCoproduct_of_functors_alt2
     BinCoproductsHSET has_homsets_HSET has_homsets_HSET BinProductsHSET F G) : cocont_functor_hset_scope.

Notation "1" := (unitHSET) : cocont_functor_hset_scope.
Notation "0" := (emptyHSET) : cocont_functor_hset_scope.
