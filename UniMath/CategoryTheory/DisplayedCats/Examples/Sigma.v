Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
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

Lemma E_mor_eq
  {x y xx yy}
  {xxx : E (x ,, xx)}
  {yyy : E (y ,, yy)}
  (f : z_iso x y)
  (g := inv_from_z_iso f)
  {ff gg fff ggg}
  {H1 : compose (C := total_category D) (a := (_ ,, _)) (b := (_ ,, _)) (c := (_ ,, _)) (pr1 f ,, ff) (g ,, gg) = identity ((x ,, xx) : total_category _)}
  (H2 : comp_disp (D := sigma_disp_cat) (xx := (xx ,, xxx)) (yy := (yy ,, yyy)) (zz := (xx ,, xxx)) (ff ,, fff) (gg ,, ggg) = transportb _ (pr122 f) (id_disp ((xx ,, xxx) : sigma_disp_cat _)))
  : fff ;; ggg = transportb _ H1 (id_disp _).
Proof.
  induction (total2_paths_equiv _ _ _ H2) as [H3 H4].
  use (transportb_transpose_right (e := H3) H4 @ _).
  unfold transportb.
  simpl.
  apply transportf_transpose_right.
  rewrite pr2_transportf_sigma_disp,
    (functtransportf _ _ (two_arg_paths_f _ _)),
    (functtransportf _ _ (!H3)),
    transport_b_f,
    transport_f_f.
  apply transportf_set.
  apply (homset_property (total_category _)).
Qed.

Definition sigma_iso_to_iso
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (f : z_iso x y)
  (fff : z_iso_disp f xxx yyy)
  : ∑ (ff : z_iso_disp f (pr1 xxx) (pr1 yyy)), z_iso_disp (total_z_iso f ff (xx := (x ,, pr1 xxx)) (yy := (y ,, pr1 yyy))) (pr2 xxx) (pr2 yyy).
Proof.
  use tpair.
  - repeat use tpair.
    + exact (pr11 fff).
    + exact (pr112 fff).
    + abstract exact (maponpaths pr1 (pr122 fff) @ pr1_transportf_sigma_disp _ _).
    + abstract exact (maponpaths pr1 (pr222 fff) @ pr1_transportf_sigma_disp _ _).
  - repeat use tpair.
    + exact (pr21 fff).
    + exact (pr212 fff).
    + exact (E_mor_eq (z_iso_inv f) (pr122 fff)).
    + exact (E_mor_eq f (pr222 fff)).
Defined.

Lemma sigma_mor_eq
  {x y f g}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  {fff : xxx -->[f] yyy}
  {ggg : yyy -->[g] xxx}
  {H1 : f · g = identity x}
  (H2 : pr1 fff ;; pr1 ggg = transportb (mor_disp (pr1 xxx) (pr1 xxx)) H1 (id_disp (pr1 xxx)))
  (H3 : pr2 fff ;; pr2 ggg =
    transportb (mor_disp (pr2 xxx) (pr2 xxx))
    (total2_paths_b (s := ((f ,, pr1 fff) : total_category D ⟦(_ ,, _), (_ ,, _)⟧) · ((g ,, pr1 ggg) : total_category D ⟦(_ ,, _), (_ ,, _)⟧)) (s' := identity ((_,, _) : total_category D)) H1 H2)
    (id_disp (pr2 xxx)))
  : fff ;; ggg =
  transportb (mor_disp xxx xxx) H1 (id_disp xxx).
Proof.
  use total2_paths_f.
  - unfold transportb.
    rewrite pr1_transportf_sigma_disp.
    exact H2.
  - use (maponpaths _ H3 @ _).
    unfold transportb.
    rewrite pr2_transportf_sigma_disp.
    rewrite (functtransportf _ _ (internal_paths_rew_r _ _ _ _ _ _)).
    apply transportf_transpose_right.
    rewrite transport_b_f,
      transport_f_f.
    apply transportf_set,
      (homset_property (total_category _)).
Qed.

Definition iso_to_sigma_is_disp_inverse
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  {f : z_iso x y}
  (fff : ∑ (ff : z_iso_disp f (pr1 xxx) (pr1 yyy)), z_iso_disp (total_z_iso f ff (xx := (x ,, pr1 xxx)) (yy := (y ,, pr1 yyy))) (pr2 xxx) (pr2 yyy))
  : is_disp_inverse (D := sigma_disp_cat) f (pr11 fff,, pr12 fff) (pr121 fff,, pr122 fff).
Proof.
  use tpair;
    use sigma_mor_eq.
  - exact (pr1 (pr221 fff)).
  - use (pr1 (pr222 fff) @ _).
    apply transportf_transpose_right.
    use (transport_b_b _ _ _ _ @ _).
    exact (transportf_set _ _ _ (homset_property _ _ _)).
  - exact (pr2 (pr221 fff)).
  - use (pr2 (pr222 fff) @ _).
    apply transportf_transpose_right.
    use (transport_b_b _ _ _ _ @ _).
    exact (transportf_set _ _ _ (homset_property _ _ _)).
Qed.

Definition iso_to_sigma_iso
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (f : z_iso x y)
  (fff : ∑ (ff : z_iso_disp f (pr1 xxx) (pr1 yyy)), z_iso_disp (total_z_iso f ff (xx := (x ,, pr1 xxx)) (yy := (y ,, pr1 yyy))) (pr2 xxx) (pr2 yyy))
  : z_iso_disp f xxx yyy
  := _ ,, _ ,, iso_to_sigma_is_disp_inverse fff.

Definition sigma_disp_z_iso_equiv
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (f : z_iso x y)
  : z_iso_disp f xxx yyy
  ≃ ∑ (ff : z_iso_disp f (pr1 xxx) (pr1 yyy)), z_iso_disp (total_z_iso f ff (xx := (x ,, pr1 xxx)) (yy := (y ,, pr1 yyy))) (pr2 xxx) (pr2 yyy).
Proof.
  use weq_iso.
  - exact (sigma_iso_to_iso f).
  - exact (iso_to_sigma_iso f).
  - abstract (
      intro;
      use (subtypePairEquality' _ (isaprop_is_z_iso_disp _ _));
      now use (total2_paths_f (idpath _))
    ).
  - abstract (
      intro fff;
      use (total2_paths_f (subtypePairEquality' (idpath _) (isaprop_is_z_iso_disp _ _) : pr1 (sigma_iso_to_iso _ (iso_to_sigma_iso f fff)) = _));
      use (subtypePairEquality' _ (isaprop_is_z_iso_disp _ _));
      use (pr1_transportf (B := λ ff, (pr2 xxx) -->[_ ,, pr1 ff] _) _ _ @ _);
      use (functtransportf _ _ _ _ @ _);
      exact (transportf_set _ _ _ (homset_property _ _ _))
    ).
Defined.

(** ** Univalence *)

(* Local Open Scope hide_transport_scope. *)

Lemma is_univalent_sigma_disp (DD : is_univalent_disp D) (EE : is_univalent_disp E)
  : is_univalent_disp sigma_disp_cat.
Proof.
  apply is_univalent_disp_from_fibers.
  intros x xx yy.
  use weqhomot.
  - induction xx as [xx xxx], yy as [yy yyy].
    (* TODO: a pure transport lemma; maybe break out? *)
    pose (i := λ (ee : xx = yy), (total2_paths2_f (idpath x) ee)).
    assert (H1 : (xx,, xxx : sigma_disp_cat _) ╝ yy,, yyy
      ≃ (∑ ee, transportf E (i ee) xxx = yyy)).
    {
      apply weqfibtototal.
      intro ee.
      induction (ee : xx = yy).
      apply idweq.
    }
    (* TODO: maybe break out this lemma on [idtoiso]? *)
    assert (H2 : (∑ ee, z_iso_disp (idtoiso (C := total_category _) (i ee)) xxx yyy) ≃ ∑ ee : xx = yy, z_iso_disp (@total_z_iso _ D (_,,_) (_,,_) _ (idtoiso_disp (idpath _) ee)) xxx yyy).
    {
      apply weqfibtototal.
      intro ee.
      refine ((transportf (λ I, z_iso_disp I xxx yyy) _) ,, (isweqtransportf (λ I, z_iso_disp I _ _) _)).
      induction ee.
      now apply (z_iso_eq (C := total_category D)).
    }
    exact (
      (invweq (sigma_disp_z_iso_equiv (xxx := (_ ,, _)) (yyy := (_ ,, _)) _))
      ∘ (weqfp (make_weq _ (DD _ _ (idpath _) _ _)) _)
      ∘ H2
      ∘ (weqfibtototal _ _ (λ _, make_weq _ (EE _ _ _ _ _)))
      ∘ H1
      ∘ total2_paths_equiv _ _ _).
  - assert (lemma2 : ∏ i i' (e : i = i') ii,
      pr1 (transportf (λ _, z_iso_disp _ (pr2 xx) (pr2 yy)) e ii)
      = transportf _ (maponpaths pr1 e) (pr1 ii)).
    {
      intros i i' e.
      now induction e.
    }
    intro ee.
    apply eq_z_iso_disp.
    induction ee.
    cbn.
    apply maponpaths.
    refine (lemma2 _ (total_z_iso _ (identity_z_iso_disp _)) _ _ @ _).
    refine (maponpaths_2 (y' := idpath _) _ _ _).
    apply (homset_property (total_category D) _ _).
Qed.

End Sigma.
