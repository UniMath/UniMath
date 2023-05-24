
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
Local Open Scope weq_scope.

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

(** ** Equivalence of iso's via the total categories *)

Definition total_sigma_functor
  : functor (total_category sigma_disp_cat) (total_category E).
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ x, (pr1 x ,, _) ,, pr22 x).
    + exact (λ _ _ f, (pr1 f ,, _) ,, pr22 f).
  - abstract (use tpair; now repeat intro).
Defined.

Lemma total_sigma_functor_fully_faithful : fully_faithful total_sigma_functor.
Proof.
  do 2 intro.
  use isweq_iso.
  - exact (λ f, _ ,, pr21 f ,, pr2 f).
  - now intro.
  - now intro.
Qed.

Definition sigma_disp_z_iso_weq
  {x y}
  (xxx : sigma_disp_cat x)
  (yyy : sigma_disp_cat y)
  : (∑ f, z_iso_disp f xxx yyy) ≃ (∑ f, z_iso_disp f (pr2 xxx) (pr2 yyy))
  :=  (invweq (total_z_iso_equiv (D := E) ((x ,, pr1 xxx) ,, pr2 xxx) ((y ,, pr1 yyy) ,, pr2 yyy)))
    ∘ (weq_ff_functor_on_z_iso total_sigma_functor_fully_faithful (x ,, xxx) (y ,, yyy))
    ∘ (total_z_iso_equiv (D := sigma_disp_cat) (x ,, xxx) (y ,, yyy)).

(*
An attempt at turning the equivalence above into an equivalence that preserves the base iso, which would be more suitable for our purpose.

Definition sigma_disp_z_iso_weq2
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (f : z_iso x y)
  : (z_iso_disp f xxx yyy) ≃ (∑ (ff : z_iso_disp f (pr1 xxx) (pr1 yyy)), z_iso_disp (total_z_iso f ff (xx := (x ,, pr1 xxx)) (yy := (y ,, pr1 yyy))) (pr2 xxx) (pr2 yyy)).
Proof.
  use weq_iso.
  - intro fff.
    pose (gg := (sigma_disp_z_iso_weq xxx yyy (f ,, fff))).
    assert (pr111 gg = pr1 f).
    {
      cbn.

    }
    cbn in gg.
    use tpair.
    + (* Impossible, since we don't necessarily preserve f *)
      use total_z_iso.
      * exact f.
      *
      simpl.
    exists ()
Defined. *)

(** ** Equivalence of equalities *)

Definition sigma_equality_to_equality
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (H : (∑ (H1 : x = y), transportf _ H1 xxx = yyy))
  : (∑ (H1 : (x ,, pr1 xxx) = (y ,, pr1 yyy)), transportf _ H1 (pr2 xxx) = (pr2 yyy)).
Proof.
  induction H as [H1 H2], H1, H2.
  now use tpair.
Defined.

Definition equality_to_sigma_equality
  {xx yy}
  {xxx : E xx}
  {yyy : E yy}
  (H : (∑ (H1 : xx = yy), transportf _ H1 xxx = yyy))
  : (∑ (H1 : pr1 xx = pr1 yy), transportf _ H1 ((pr2 xx ,, xxx) : sigma_disp_cat _) = (pr2 yy ,, yyy)).
Proof.
  induction H as [H1 H2], H1, H2.
  now use tpair.
Defined.

Lemma sigma_equality_to_equality_and_back
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (H : (∑ (H1 : x = y), transportf _ H1 xxx = yyy))
  : equality_to_sigma_equality (sigma_equality_to_equality H) = H.
Proof.
  now induction H as [H1 H2], H1, H2.
Qed.

Lemma equality_to_sigma_equality_and_back
  {xx yy}
  {xxx : E xx}
  {yyy : E yy}
  (H : (∑ (H1 : xx = yy), transportf _ H1 xxx = yyy))
  : sigma_equality_to_equality (equality_to_sigma_equality H) = H.
Proof.
  now induction H as [H1 H2], H1, H2.
Qed.

Definition equality_weq
  {x y xx yy}
  (xxx : E (x ,, xx))
  (yyy : E (y ,, yy))
  : (∑ (H1 : x = y), transportf _ H1 (xx ,, xxx : sigma_disp_cat _) = (yy ,, yyy))
  ≃ (∑ (H1 : (x ,, xx) = (y ,, yy)), transportf _ H1 xxx = yyy)
  := weq_iso
    _
    _
    sigma_equality_to_equality_and_back
    equality_to_sigma_equality_and_back.

(** ** One-way transport of iso's *)

Lemma sigma_mor_eq
  {x y xx yy f ff gg}
  {xxx : E (x ,, xx)}
  {yyy : E (y ,, yy)}
  {fff ggg}
  {H1 : f = f}
  {H2 : ff = gg}
  (H3 : transportf (λ qq, mor_disp xxx yyy (f,, qq)) H2 fff = ggg)
  : (ff ,, fff)
  = transportb
    (mor_disp (D := sigma_disp_cat) ((xx ,, xxx)) (yy ,, yyy))
    H1
    (gg ,, ggg).
Proof.
  induction H2, H3.
  use total2_paths_f.
  - unfold transportb.
    now rewrite (transportf_set _ _ _ (homset_property _ _ _)).
  - unfold transportb.
    use (functtransportf _ _ _ _ @ _).
    use (_ @ !(pr2_transportf_sigma_disp _ _)).
    apply (maponpaths (λ H, transportf _ H _)).
    apply homset_property.
Qed.

Definition sigma_functor
  : disp_functor (pr1_category D) E sigma_disp_cat.
Proof.
  use tpair.
  - use tpair.
    + exact (λ d e, pr2 d ,, e).
    + exact (λ _ _ _ _ ff fff, pr2 ff ,, fff).
  - abstract (
      use tpair;
      repeat intro;
      now use sigma_mor_eq
    ).
Defined.

Definition transport_iso
  {xx yy} {xxx : E xx} {yyy} {ff : z_iso xx yy}
  (fff : z_iso_disp ff xxx yyy)
  : (∑ f, z_iso_disp f (sigma_functor _ xxx) (sigma_functor _ yyy))
  := functor_on_z_iso (pr1_category D) ff ,, disp_functor_on_z_iso_disp sigma_functor fff.

(* Proof that both ways of transporting iso's are equivalent *)
Lemma iso_transports_eq
  {xx yy}
  {xxx : E xx}
  {yyy : E yy}
  {ff : z_iso xx yy}
  (fff : z_iso_disp ff xxx yyy)
  : transport_iso fff = invmap (sigma_disp_z_iso_weq (pr2 xx ,, xxx) (pr2 yy ,, yyy)) (ff ,, fff).
Proof.
  apply pathsweq1.
  simpl.
  use (!(pathsweq1 _ _ _ _)).
  simpl.
  use subtypePairEquality'.
  - simpl.
    apply idpath.
  - simpl.
    apply (isaprop_is_z_isomorphism (C := total_category E)).
Qed.

(*
  An attempt to prove that this way of transporting preserves the base iso, which should allow us to actually use this for univalence

Lemma transport_iso_preserves_form
  {xx yy}
  {xxx : E xx}
  {yyy : E yy}
  {ff}
  (fff : z_iso_disp ff xxx yyy)
  {H1 : is_z_isomorphism (pr11 ff)}
  {H2 : is_z_iso_disp (D := sigma_disp_cat) (pr11 ff ,, H1) ((pr21 ff ,, pr1 fff) : ((_ ,, _) : sigma_disp_cat _) -->[_] (_ ,, _))}
  : (transport_iso fff) = ((pr11 ff ,, H1) ,, (((pr21 ff ,, pr1 fff) : ((_ ,, _) : sigma_disp_cat _) -->[_] (_ ,, _)) ,, H2)).
Proof.
  use total2_paths_f.
  - now use (subtypePairEquality' _ (isaprop_is_z_isomorphism _)).
  - use (subtypePairEquality' _ (isaprop_is_z_iso_disp _ _)).
    use total2_paths_f.
    + simpl.
      apply idpath.
    apply idpath.
Qed.
*)

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
