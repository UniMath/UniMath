
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** * Sigmas of displayed (pre)categories *)
Section Sigma.

Context {C : category}
        {D : disp_cat C}
        (E : disp_cat (total_category D)).

Definition sigma_disp_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, ∑ (d : D c), (E (c,,d))).
  intros x y xx yy f.
  exact (∑ (fD : pr1 xx -->[f] pr1 yy),
                (pr2 xx -->[f,,fD] pr2 yy)).
Defined.

Definition sigma_disp_cat_id_comp
  : disp_cat_id_comp _ sigma_disp_cat_ob_mor.
Proof.
  apply tpair.
  - intros x xx.
    exists (id_disp _). exact (id_disp (pr2 xx)).
  - intros x y z f g xx yy zz ff gg.
    exists (pr1 ff ;; pr1 gg). exact (pr2 ff ;; pr2 gg).
Defined.

Definition sigma_disp_cat_data : disp_cat_data C
  := (_ ,, sigma_disp_cat_id_comp).


Definition sigma_disp_cat_axioms
  : disp_cat_axioms _ sigma_disp_cat_data.
Proof.
  repeat apply tpair.
  - intros x y f [xx xxx] [yy yyy] [ff fff]; simpl in ff, fff.
    use total2_reassoc_paths'.
    + simpl. apply id_left_disp.
    + simpl. apply (pathscomp0 (id_left_disp fff)).
      apply maponpaths_2. apply homset_property.
  - intros x y f [xx xxx] [yy yyy] [ff fff]; simpl in ff, fff.
    use total2_reassoc_paths'.
    + simpl. apply id_right_disp.
    + simpl. apply (pathscomp0 (id_right_disp fff)).
      apply maponpaths_2. apply homset_property.
  - intros x y z w f g h [xx xxx] [yy yyy] [zz zzz] [ww www] [ff fff] [gg ggg] [hh hhh].
    simpl in ff, fff, gg, ggg, hh, hhh.
    use total2_reassoc_paths'.
    + simpl. apply assoc_disp.
    + apply (pathscomp0 (assoc_disp fff ggg hhh)).
      apply maponpaths_2. apply homset_property.
  - intros. apply isaset_total2.
    + apply homsets_disp.
    + intros. apply homsets_disp.
Qed.

Definition sigma_disp_cat : disp_cat C
  := (_ ,, sigma_disp_cat_axioms).

(** ** Equivalence between the total categories *)
Definition total_sigma_disp_cat_adjunction_data
  : adjunction_data (total_category (sigma_disp_cat)) (total_category E).
Proof.
  use make_adjunction_data.
  - use make_functor.
    + use make_functor_data.
      * exact (λ x, (pr1 x ,, _) ,, pr22 x).
      * exact (λ _ _ f, (pr1 f ,, _) ,, pr22 f).
    + abstract (use tpair; now repeat intro).
  - use make_functor.
    + use make_functor_data.
      * exact (λ x, _ ,, pr21 x ,, pr2 x).
      * exact (λ _ _ f, _ ,, pr21 f ,, pr2 f).
    + abstract (use tpair; now repeat intro).
  - use make_nat_trans.
    + exact identity.
    + abstract (do 3 intro; now rewrite id_left, id_right).
  - use make_nat_trans.
    + exact identity.
    + abstract (do 3 intro; now rewrite id_left, id_right).
Defined.

Lemma total_sigma_disp_cat_forms_equivalence
  : forms_equivalence total_sigma_disp_cat_adjunction_data.
Proof.
  exact (make_forms_equivalence
    total_sigma_disp_cat_adjunction_data
    is_z_isomorphism_identity
    is_z_isomorphism_identity).
Qed.

Definition equivalence_total_sigma_disp_cat
  : equivalence_of_cats (total_category sigma_disp_cat) (total_category E)
  := make_equivalence_of_cats _ total_sigma_disp_cat_forms_equivalence.

Definition sigmapr1_disp_functor_data
  : disp_functor_data (functor_identity C) sigma_disp_cat D.
Proof.
  use tpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition sigmapr1_disp_functor_axioms
  : disp_functor_axioms sigmapr1_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition sigmapr1_disp_functor
  : disp_functor (functor_identity C) sigma_disp_cat D
:= (sigmapr1_disp_functor_data,, sigmapr1_disp_functor_axioms).

(* TODO: complete [sigmapr2_disp]; will be a [functor_lifting], not a [disp_functor]. *)

(** ** Transport and isomorphism lemmas *)

Lemma pr1_transportf_sigma_disp {x y : C} {f f' : x --> y} (e : f = f')
    {xxx : sigma_disp_cat x} {yyy} (fff : xxx -->[f] yyy)
  : pr1 (transportf _ e fff) = transportf _ e (pr1 fff).
Proof.
  destruct e; apply idpath.
Qed.

Lemma pr2_transportf_sigma_disp {x y : C} {f f' : x --> y} (e : f = f')
    {xxx : sigma_disp_cat x} {yyy} (fff : xxx -->[f] yyy)
  : pr2 (transportf _ e fff)
  = transportf (λ ff, pr2 xxx -->[ff] _ ) (two_arg_paths_f (*total2_paths2*) e (! pr1_transportf_sigma_disp e fff))
      (pr2 fff).
Proof.
  destruct e. apply pathsinv0.
  etrans. apply maponpaths_2, maponpaths, maponpaths.
  apply (homsets_disp _ _ _ _ _ _ (idpath _)).
  apply idpath.
Qed.


(** ** Univalence *)

Local Open Scope hide_transport_scope.

Definition is_z_iso_sigma_disp_aux1
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : z_iso x y} (fff : xxx -->[f] yyy)
    (ii : is_z_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : z_iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_z_iso_disp (@total_z_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  : yyy -->[inv_from_z_iso f] xxx.
Proof.
  exists (inv_mor_disp_from_z_iso ii).
  set (ggg := inv_mor_disp_from_z_iso iii).
  exact (transportf _ (inv_mor_total_z_iso _ _) ggg).
Defined.

Lemma is_z_iso_sigma_disp_aux2
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : z_iso x y} (fff : xxx -->[f] yyy)
    (ii : is_z_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : z_iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_z_iso_disp (@total_z_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  :   (is_z_iso_sigma_disp_aux1 fff ii iii) ;; fff
    = transportb _ (z_iso_after_z_iso_inv f) (id_disp yyy)
  ×
      fff ;; (is_z_iso_sigma_disp_aux1 fff ii iii)
    = transportb _ (z_iso_inv_after_z_iso f) (id_disp xxx).
Proof.
  split.
  - use total2_paths_f.
    + abstract ( etrans;
        [ apply z_iso_disp_after_inv_mor
        | apply pathsinv0, pr1_transportf_sigma_disp]).
    + etrans. 2: apply @pathsinv0, pr2_transportf_sigma_disp.
      etrans. apply maponpaths.
        use (mor_disp_transportf_postwhisker
          (@inv_mor_total_z_iso _ _ (_,,_) (_,,_) f ffi) _ (pr2 fff)).
      etrans. apply functtransportf.
      etrans. apply transport_f_f.
      etrans. eapply transportf_bind.
        apply (z_iso_disp_after_inv_mor iii).
      apply maponpaths_2, (@homset_property (total_category D)).
  - use total2_paths_f; cbn.
    + abstract ( etrans;
        [ apply inv_mor_after_z_iso_disp
        | apply pathsinv0, pr1_transportf_sigma_disp ]).
    + etrans. 2: apply @pathsinv0, pr2_transportf_sigma_disp.
      etrans. apply maponpaths.
      use (mor_disp_transportf_prewhisker
        (@inv_mor_total_z_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff) _).
      etrans. apply functtransportf.
      etrans. apply transport_f_f.
      etrans. eapply transportf_bind.
        apply (inv_mor_after_z_iso_disp iii).
      apply maponpaths_2, (@homset_property (total_category D)).
Qed.

Lemma is_z_iso_sigma_disp
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : z_iso x y} (fff : xxx -->[f] yyy)
    (ii : is_z_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : z_iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_z_iso_disp (@total_z_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  : is_z_iso_disp f fff.
Proof.
  exists (is_z_iso_sigma_disp_aux1 fff ii iii).
  apply is_z_iso_sigma_disp_aux2.
Defined.

Definition sigma_disp_z_iso
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    {f : z_iso x y} (ff : z_iso_disp f (pr1 xx) (pr1 yy))
    (fff : z_iso_disp (@total_z_iso _ _ (_,,_) (_,,_) f ff) (pr2 xx) (pr2 yy))
  : z_iso_disp f xx yy.
Proof.
  exists (pr1 ff,, pr1 fff). use is_z_iso_sigma_disp; cbn.
  - exact (pr2 ff).
  - exact (pr2 fff).
Defined.

Definition sigma_disp_z_iso_map
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : z_iso x y)
  : (∑ ff : z_iso_disp f (pr1 xx) (pr1 yy),
       z_iso_disp (@total_z_iso _ _ (_,,_) (_,,_) f ff) (pr2 xx) (pr2 yy))
  -> z_iso_disp f xx yy
:= λ ff, sigma_disp_z_iso _ _ (pr1 ff) (pr2 ff).

Lemma sigma_disp_isweq_z_iso
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : z_iso x y)
  : isweq (sigma_disp_z_iso_map xx yy f).
Proof.
Abort.

(*
Definition sigma_disp_z_iso_equiv
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : z_iso x y)
:= make_weq _ (sigma_disp_isweq_z_iso xx yy f).
*)

(*
Lemma is_univalent_sigma_disp (DD : is_univalent_disp D) (EE : is_univalent_disp E)
  : is_univalent_disp sigma_disp_cat.
Proof.
  apply is_univalent_disp_from_fibers.
  intros x xx yy.
  use weqhomot.
  - destruct xx as [xx xxx], yy as [yy yyy].
     use (@weqcomp _ (∑ ee : xx = yy, transportf (λ r, E (x,,r)) ee xxx = yyy) _ _ _).
      refine (total2_paths_equiv _ _ _).
    set (i := fun (ee : xx = yy) => (total2_paths2 (idpath _) ee)).
    apply @weqcomp with
        (∑ ee : xx = yy, transportf _ (i ee) xxx = yyy).
      apply weqfibtototal; intros ee.
      refine (_ ,, isweqpathscomp0l _ _).
      (* TODO: a pure transport lemma; maybe break out? *)
      destruct ee; apply idpath.
    apply @weqcomp with (∑ ee : xx = yy,
             iso_disp (@idtoiso (total_category _) (_,,_) (_,,_) (i ee)) xxx yyy).
      apply weqfibtototal; intros ee.
      exists (fun (eee : transportf _ (i ee) xxx = yyy) => idtoiso_disp _ eee).
      apply EE.
    apply @weqcomp with (∑ ee : xx = yy, iso_disp
         (@total_iso _ D (_,,_) (_,,_) _ (idtoiso_disp (idpath _) ee)) xxx yyy).
      apply weqfibtototal; intros ee.
      use tpair.
        refine (transportf (λ I, iso_disp I xxx yyy) _).
        unfold i.
      (* TODO: maybe break out this lemma on [idtoiso]? *)
      (* Note: [abstract] here is to speed up a [cbn] below. *)
        destruct ee. abstract (apply eq_iso, idpath).
      exact (isweqtransportf (λ I, iso_disp I xxx yyy) _).
    apply (@weqcomp _ (∑ f : iso_disp (identity_iso x) xx yy,
                      (iso_disp (@total_iso _ D (_,,_) (_,,_) _ f) xxx yyy)) _).
      refine (weqfp (make_weq _ _) _). refine (DD _ _ (idpath _) _ _).
    apply (sigma_disp_iso_equiv (_,,_) (_,,_) _).
  - assert (lemma2 : forall i i' (e : i = i') ii,
                 pr1 (transportf (λ i, iso_disp i (pr2 xx) (pr2 yy)) e ii)
                 = transportf _ (maponpaths pr1 e) (pr1 ii)).
      intros; destruct e; apply idpath.
    intros ee; apply eq_iso_disp.
    destruct ee, xx as [xx xxx]; cbn.
    apply maponpaths.
    etrans. cbn in lemma2.
    (* This [match] is to supply the 3rd argument of [lemma2], without referring to the identifier auto-generated by [abstract] above. *)
    match goal with |[ |- pr1 (transportf _ ?H _) = _ ]
      => apply (lemma2 _ _ H _) end.
    refine (@maponpaths_2 _ _ _ _ _ (idpath _) _ _).
    etrans. use maponpaths. apply eq_iso, idpath.
      apply isaset_iso, homset_property.
   apply (@homset_property (total_category _) (_,,_) (_,,_)).
Qed.
*)

End Sigma.
