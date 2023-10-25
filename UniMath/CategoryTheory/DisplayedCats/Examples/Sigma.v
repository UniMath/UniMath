(* For displayed categories D over C and E over total_category D,
  the sigma category of E is a displayed category over C,
  with dependent pairs of objects and morphims of D and E as objects and morphisms.
  This file defines and proves
  - The sigma category [sigma_disp_cat]
  - The displayed projection functor from sigma to D [sigmapr1_disp_functor]
  - Displayed univalence for sigma [is_univalent_sigma_disp]
  - Sigma creates limits [creates_limits_sigma_disp_cat] *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.

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

(** ** Limits *)
Definition sigma_to_E_total_functor
  : total_category sigma_disp_cat ⟶ total_category E.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro t.
      exact ((pr1 t ,, pr12 t) ,, pr22 t).
    + intros ? ? t.
      exact ((pr1 t ,, pr12 t) ,, pr22 t).
  - abstract now use tpair; intro.
Defined.

Definition E_to_sigma_total_functor
  : total_category E ⟶ total_category sigma_disp_cat.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro t.
      exact (pr11 t ,, pr21 t ,, pr2 t).
    + intros ? ? t.
      exact (pr11 t ,, pr21 t ,, pr2 t).
  - abstract now use tpair; intro.
Defined.

Section Limits.
  Context (D' := sigma_disp_cat).
  Context {J : graph}.
  Context {d : diagram J (total_category D')}.
  Context {L : LimCone (mapdiagram (pr1_category _) d)}.

  Context (HD : creates_limit (mapdiagram (total_functor sigmapr1_disp_functor) d) L).
  Context (HE : creates_limit (mapdiagram sigma_to_E_total_functor d) (total_limit _ HD)).

  Definition tip_sigma_disp_cat
    : D' (lim L)
    := pr11 HD ,, pr11 HE.

  Definition cone_sigma_disp_cat
    (j : vertex J)
    : tip_sigma_disp_cat -->[limOut L j] pr2 (dob d j)
    := pr121 HD j ,, pr121 HE j.

  Lemma forms_cone_sigma_disp_cat
    (u v : vertex J)
    (e : edge u v)
    : compose (C := total_category sigma_disp_cat) (a := _ ,, _) (_ ,, cone_sigma_disp_cat u) (dmor d e) = (_ ,, cone_sigma_disp_cat v).
  Proof.
    apply (pr2 (mapcone E_to_sigma_total_functor _ (make_cone _ (pr221 HE)))).
  Qed.

  Section Arrow.

    Context (d' : total_category D').
    Context (d'_cone : cone d d').

    Let d_cone := (make_LimCone _ _ _ (pr2 HE)).
    Let e_cone := mapcone sigma_to_E_total_functor _ d'_cone.

    Definition sigma_lim_arrow
      : total_category D'⟦d', lim L,, tip_sigma_disp_cat⟧
      := (# E_to_sigma_total_functor)%cat (limArrow d_cone _ e_cone).

    Lemma sigma_lim_arrow_commutes
      : is_cone_mor d'_cone
        (make_cone _ forms_cone_sigma_disp_cat)
        sigma_lim_arrow.
    Proof.
      intro u.
      exact (maponpaths (# E_to_sigma_total_functor)%cat (limArrowCommutes d_cone _ e_cone u)).
    Qed.

    Lemma sigma_lim_arrow_unique
      (t : ∑ x, is_cone_mor d'_cone (make_cone _ forms_cone_sigma_disp_cat) x)
      : t = sigma_lim_arrow ,, sigma_lim_arrow_commutes.
    Proof.
      use subtypePairEquality.
      {
        intro.
        apply impred_isaprop.
        intro.
        apply homset_property.
      }
      pose (f' := (# sigma_to_E_total_functor)%cat (pr1 t)).
      pose (Hf' := λ u, maponpaths (# sigma_to_E_total_functor)%cat (pr2 t u)).
      pose (uniq := limArrowUnique d_cone _ e_cone f' Hf').
      exact (maponpaths (# E_to_sigma_total_functor)%cat uniq).
    Qed.

  End Arrow.

  Definition is_lim_cone_sigma_disp_cat
    : isLimCone _ _ (make_cone _ (forms_cone_sigma_disp_cat)).
  Proof.
    intros d' d'_cone.
    use ((_ ,, _) ,, _).
    - exact (sigma_lim_arrow d' d'_cone).
    - exact (sigma_lim_arrow_commutes d' d'_cone).
    - exact (sigma_lim_arrow_unique d' d'_cone).
  Defined.

End Limits.

Definition creates_limits_sigma_disp_cat
  {J : graph}
  (F : diagram J (total_category sigma_disp_cat))
  (L : LimCone (mapdiagram (pr1_category _) F))
  (HD : creates_limit (mapdiagram (total_functor sigmapr1_disp_functor) F) L)
  (HE : creates_limit (mapdiagram sigma_to_E_total_functor F) (total_limit _ HD))
  : creates_limit F L
  := make_creates_limit
    (tip_sigma_disp_cat HD HE)
    (cone_sigma_disp_cat HD HE)
    (forms_cone_sigma_disp_cat HD HE)
    (is_lim_cone_sigma_disp_cat HD HE).

(** ** Univalence *)
(** *** Characterization of the isos of sigma_disp_cat *)
Lemma E_mor_eq
  {x y xx yy}
  {xxx : E (x ,, xx)}
  {yyy : E (y ,, yy)}
  (xxx' := (xx ,, xxx) : sigma_disp_cat _)
  (yyy' := (yy ,, yyy) : sigma_disp_cat _)
  (f : z_iso x y)
  (g := inv_from_z_iso f)
  {ff gg fff ggg}
  {H1 : compose (C := total_category D) (a := (_ ,, _)) (b := (_ ,, _)) (c := (_ ,, _))
    (z_iso_mor f ,, ff) (g ,, gg) = identity _}
  (H2 : comp_disp (D := sigma_disp_cat) (xx := (xx ,, xxx)) (yy := (yy ,, yyy)) (zz := (xx ,, xxx))
    (ff ,, fff) (gg ,, ggg) = transportb _ (z_iso_inv_after_z_iso f) (id_disp _))
  : fff ;; ggg = transportb _ H1 (id_disp _).
Proof.
  induction (total2_paths_equiv _ _ _ H2) as [H3 H4].
  refine (transportb_transpose_right (e := H3) H4 @ _).
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
  : ∑ ff, z_iso_disp (total_z_iso f ff (xx := (_ ,, _)) (yy := (_ ,, _))) (pr2 xxx) (pr2 yyy).
Proof.
  use tpair.
  - repeat use tpair.
    + exact (pr1 (mor_disp_from_z_iso fff)).
    + exact (pr1 (inv_mor_disp_from_z_iso fff)).
    + abstract exact (maponpaths _ (z_iso_disp_after_inv_mor fff) @ pr1_transportf_sigma_disp _ _).
    + abstract exact (maponpaths _ (inv_mor_after_z_iso_disp fff) @ pr1_transportf_sigma_disp _ _).
  - repeat use tpair.
    + exact (pr2 (mor_disp_from_z_iso fff)).
    + exact (pr2 (inv_mor_disp_from_z_iso fff)).
    + exact (E_mor_eq (z_iso_inv f) (z_iso_disp_after_inv_mor fff)).
    + exact (E_mor_eq f (inv_mor_after_z_iso_disp fff)).
Defined.

Lemma sigma_mor_eq
  {x y f g}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  {fff : xxx -->[f] yyy}
  {ggg : xxx -->[g] yyy}
  {H1 : f = g}
  {H2}
  (H3 : pr2 fff = transportb _ (total2_paths_b (s := (_ ,, _)) (s' := (_ ,, _)) H1 H2) (pr2 ggg))
  : fff = transportb _ H1 ggg.
Proof.
  use total2_paths_f.
  - refine (H2 @ !_).
    apply pr1_transportf_sigma_disp.
  - refine (maponpaths _ H3 @ _ @ !(pr2_transportf_sigma_disp _ _)).
    refine (functtransportf _ _ _ _ @ _).
    apply transportf_transpose_right.
    refine (transport_b_f _ _ _ _ @ transport_f_f _ _ _ _ @ _).
    exact (transportf_set _ _ _ (homset_property (total_category _) (_ ,, _) (_ ,, _))).
Qed.

Definition iso_to_sigma_is_disp_inverse
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  {f : z_iso x y}
  (fff : ∑ ff, z_iso_disp (total_z_iso f ff (xx := (_ ,, _)) (yy := (_ ,, _))) (pr2 xxx) (pr2 yyy))
  : is_disp_inverse (D := sigma_disp_cat) (z_iso_is_inverse_in_precat f)
    (mor_disp_from_z_iso (pr1 fff) ,, mor_disp_from_z_iso (pr2 fff))
    (inv_mor_disp_from_z_iso (pr1 fff) ,, inv_mor_disp_from_z_iso (pr2 fff)).
Proof.
  use tpair;
    use sigma_mor_eq.
  - exact (z_iso_disp_after_inv_mor (pr1 fff)).
  - refine (z_iso_disp_after_inv_mor (pr2 fff) @ _).
    apply transportf_transpose_right.
    refine (transport_b_b _ _ _ _ @ _).
    exact (transportf_set _ _ _ (homset_property _ _ _)).
  - exact (inv_mor_after_z_iso_disp (pr1 fff)).
  - refine (inv_mor_after_z_iso_disp (pr2 fff) @ _).
    apply transportf_transpose_right.
    refine (transport_b_b _ _ _ _ @ _).
    exact (transportf_set _ _ _ (homset_property _ _ _)).
Qed.

Definition iso_to_sigma_iso
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (f : z_iso x y)
  (fff : ∑ ff, z_iso_disp (total_z_iso f ff (xx := (_ ,, _)) (yy := (_ ,, _))) (pr2 xxx) (pr2 yyy))
  : z_iso_disp f xxx yyy
  := _ ,, _ ,, iso_to_sigma_is_disp_inverse fff.

Definition sigma_disp_z_iso_equiv
  {x y}
  {xxx : sigma_disp_cat x}
  {yyy : sigma_disp_cat y}
  (f : z_iso x y)
  : z_iso_disp f xxx yyy
  ≃ ∑ ff, z_iso_disp (total_z_iso f ff (xx := (_ ,, _)) (yy := (_ ,, _))) (pr2 xxx) (pr2 yyy).
Proof.
  use weq_iso.
  - exact (sigma_iso_to_iso f).
  - exact (iso_to_sigma_iso f).
  - abstract (
      intro;
      apply eq_z_iso_disp;
      now use total2_paths_f
    ).
  - abstract (
      intro;
      use total2_paths_f;
      [now apply eq_z_iso_disp | apply eq_z_iso_disp];
      refine (pr1_transportf (B := λ ff, (pr2 xxx) -->[_ ,, pr1 ff] _) _ _ @ _);
      refine (functtransportf _ _ _ _ @ _);
      exact (transportf_set _ _ _ (homset_property _ _ _))
    ).
Defined.

(* Local Open Scope hide_transport_scope. *)
(** *** The univalence proof *)
Lemma is_univalent_sigma_disp (DD : is_univalent_disp D) (EE : is_univalent_disp E)
  : is_univalent_disp sigma_disp_cat.
Proof.
  apply is_univalent_disp_from_fibers.
  intros x xx yy.
  use weqhomot.
  - induction xx as [xx xxx], yy as [yy yyy].
    refine (
      weqcomp (Y := (xx,, xxx : sigma_disp_cat x) ╝ yy,, yyy) _
      (weqcomp (Y := ∑ ee : xx = yy, z_iso_disp
        (@total_z_iso _ D (_ ,, _) (_ ,, _) _ (idtoiso_disp (idpath _) ee)) xxx yyy) _
      (weqcomp (Y := ∑ ff, (z_iso_disp (total_z_iso _ ff) xxx yyy)) _ _
    ))).
    + apply total2_paths_equiv.
    + apply weqfibtototal.
      intro ee.
      induction (ee : xx = yy).
      refine (weqcomp (Y := z_iso_disp (idtoiso (C := total_category _)
        (total2_paths2_f (idpath x) (idpath _))) xxx yyy) _ _).
      * exact (make_weq (λ ee, idtoiso_disp (idpath _) ee) (EE _ _ _ _ _)).
      * now refine (make_weq _ (isweqtransportf (λ I, z_iso_disp I _ _) (z_iso_eq _ _ _))).
    + exact (weqfp (make_weq _ (DD _ _ (idpath _) _ _)) _).
    + exact (invweq (sigma_disp_z_iso_equiv (xxx := (_ ,, _)) (yyy := (_ ,, _)) _)).
  - assert (lemma1 : ∏ i i' (e : i = i') ii,
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
    refine (maponpaths _ (lemma1 _ (total_z_iso _ (identity_z_iso_disp _)) _ _ @ _)).
    refine (maponpaths_2 (y' := idpath _) _ _ _).
    apply homset_property.
Qed.

End Sigma.
