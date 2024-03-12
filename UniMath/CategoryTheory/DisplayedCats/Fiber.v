
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp.

(** * Fiber categories *)

(** A displayed category gives a _fiber_ category over each object of the base.  These are most interesting in the case where the displayed category is an isofibration. *)

Section Fiber.

  Context {C : category}
          (D : disp_cat C)
          (c : C).

  Definition fiber_category_data : precategory_data.
  Proof.
    use tpair.
    - use tpair.
      + apply (ob_disp D c).
      + intros xx xx'. apply (mor_disp xx xx' (identity c)).
    - use tpair.
      + intros. apply id_disp.
      + cbn. intros. apply (transportf _ (id_right _ ) (comp_disp X X0)).
  Defined.

  Lemma fiber_is_precategory : is_precategory fiber_category_data.
  Proof.
    apply is_precategory_one_assoc_to_two.
    repeat split; intros; cbn.
    - etrans. apply maponpaths. apply id_left_disp.
      etrans. apply transport_f_f. apply transportf_comp_lemma_hset.
      apply (homset_property). apply idpath.
    - etrans. apply maponpaths. apply id_right_disp.
      etrans. apply transport_f_f. apply transportf_comp_lemma_hset.
      apply (homset_property). apply idpath.
    - etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths. apply assoc_disp.
      etrans. apply transport_f_f.
      apply pathsinv0.
      etrans. apply maponpaths.  apply mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      apply maponpaths_2. apply homset_property.
  Qed.

  Definition fiber_precategory : precategory := ( _ ,, fiber_is_precategory).

  Lemma has_homsets_fiber_category : has_homsets fiber_precategory.
  Proof.
    intros x y. apply homsets_disp.
  Qed.

  Definition fiber_category : category
    := ( fiber_precategory ,, has_homsets_fiber_category).


  Definition z_iso_disp_from_z_iso_fiber (a b : fiber_category) :
    z_iso a b -> z_iso_disp (identity_z_iso c) a b.
  Proof.
    intro i.
    use tpair.
    + apply (pr1 i).
    + cbn.
      use tpair.
      * apply (inv_from_z_iso i).
      * abstract (  split;
                    [ assert (XR := z_iso_after_z_iso_inv i);
                      cbn in *;
                      assert (XR' := transportf_pathsinv0' _ _ _ _ XR);
                      etrans; [ apply (!XR') |];
                      unfold transportb;
                      apply maponpaths_2; apply homset_property
                    |assert (XR := z_iso_inv_after_z_iso i);
                     cbn in *;
                     assert (XR' := transportf_pathsinv0' _ _ _ _ XR);
                     etrans; [ apply (!XR') | ];
                     unfold transportb;
                     apply maponpaths_2; apply homset_property ] ).
  Defined.

  Definition z_iso_fiber_from_z_iso_disp (a b : fiber_category) :
    z_iso a b <- z_iso_disp (identity_z_iso c) a b.
  Proof.
    intro i.
    use tpair.
    + apply (pr1 i).
    + cbn in *.
      use tpair.
      apply (inv_mor_disp_from_z_iso i).
      abstract (split; cbn;
                [
                  assert (XR := inv_mor_after_z_iso_disp i);
                  etrans; [ apply maponpaths , XR |];
                  etrans; [ apply transport_f_f |];
                  apply transportf_comp_lemma_hset;
                  try apply homset_property; apply idpath
                | assert (XR := z_iso_disp_after_inv_mor i);
                  etrans; [ apply maponpaths , XR |] ;
                  etrans; [ apply transport_f_f |];
                  apply transportf_comp_lemma_hset;
                  try apply homset_property; apply idpath
               ]).
  Defined.

  Lemma z_iso_disp_z_iso_fiber (a b : fiber_category) :
    z_iso a b ≃ z_iso_disp (identity_z_iso c) a b.
  Proof.
    exists (z_iso_disp_from_z_iso_fiber a b).
    use (isweq_iso _ (z_iso_fiber_from_z_iso_disp _ _ )).
    - intro. apply z_iso_eq. apply idpath.
    - intro. apply eq_z_iso_disp. apply idpath.
  Defined.

  (** ** Univalence *)
  Variable H : is_univalent_disp D.

  Let idto1 (a b : fiber_category) : a = b ≃ z_iso_disp (identity_z_iso c) a b
      :=
        make_weq (@idtoiso_fiber_disp _ _ _ a b) (H _ _ (idpath _ ) a b).

  Let idto2 (a b : fiber_category) : a = b -> z_iso_disp (identity_z_iso c) a b
      :=
        funcomp (λ p : a = b, idtoiso p) (z_iso_disp_z_iso_fiber a b).

  Lemma eq_idto1_idto2 (a b : fiber_category)
    : ∏ p : a = b, idto1 _ _ p = idto2 _ _ p.
  Proof.
    intro p. induction p.
    apply eq_z_iso_disp.
    apply idpath.
  Qed.

  Lemma is_univalent_fiber_cat
        (a b : fiber_category)
    :
    isweq (λ p : a = b, idtoiso p).
  Proof.
    use (twooutof3a _ (z_iso_disp_z_iso_fiber a b)).
    - use (isweqhomot (idto1 a b)).
      + intro p.
        apply eq_idto1_idto2.
      + apply weqproperty.
    - apply weqproperty.
  Defined.


  Lemma is_univalent_fiber : is_univalent fiber_category.
  Proof.
    intros a b.
    apply is_univalent_fiber_cat.
  Defined.

  Definition fiber_to_total_functor_data
  : functor_data fiber_category (total_category D).
  Proof.
    use make_functor_data.
    - exact (tpair _ c).
    - exact (λ _ _, tpair _ (identity c)).
  Defined.

  Lemma fiber_to_total_is_functor
    : is_functor fiber_to_total_functor_data.
  Proof.
    use tpair.
    - now intro.
    - do 5 intro.
      use total2_paths_f.
      + exact (!id_right _).
      + refine (transport_f_f _ _ _ _ @ _).
        now rewrite pathsinv0r.
  Qed.

  Definition fiber_to_total_functor
    : fiber_category ⟶ total_category D
    := make_functor _ fiber_to_total_is_functor.

End Fiber.

Arguments fiber_precategory {_} _ _ .
Arguments fiber_category {_} _ _ .

(* TODO: is this a terrible notation?  Probably. *)
Notation "D [{ x }]" := (fiber_category D x)(at level 3,format "D [{ x }]").


Section UnivalentFiber.
  Lemma is_univalent_disp_from_is_univalent_fiber {C : category} (D : disp_cat C)
    : (∏ (c : C), is_univalent D[{c}]) → is_univalent_disp D.
  Proof.
    intro H.
    apply is_univalent_disp_from_fibers.
    intros c xx xx'.
    specialize (H c).
    set (w := make_weq _ (H xx xx')).
    set (w' := weqcomp w (z_iso_disp_z_iso_fiber D _ xx xx')).
    apply (weqhomot _ w').
    intro e. induction e.
    apply eq_z_iso_disp. apply idpath.
  Defined.

  Definition is_univalent_disp_iff_fibers_are_univalent {C : category} (D : disp_cat C)
    : is_univalent_disp D <-> (∏ (c : C), is_univalent D[{c}]).
  Proof.
    split; intro H.
    - intro. apply is_univalent_fiber. apply H.
    - apply is_univalent_disp_from_is_univalent_fiber.
      apply H.
  Defined.
End UnivalentFiber.

Definition univalent_fiber_category
           {C : category}
           (D : disp_univalent_category C)
           (c : C)
  : univalent_category.
Proof.
  refine (D [{ c }] ,, _).
  apply is_univalent_fiber.
  exact (pr2 D).
Defined.

Proposition idtoiso_fiber_category
            {C : category}
            {D : disp_cat C}
            {x : C}
            {xx yy : D x}
            (p : xx = yy)
  : pr1 (@idtoiso (D [{ x }]) xx yy p)
    =
    pr1 (@idtoiso_disp C D x x (idpath x) xx yy p).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

(** ** Fiber functors

Functors between displayed categories induce functors between their fibers. *)
Section Fiber_Functors.
  Local Open Scope mor_disp.
  Section fix_context.

    Context {C C' : category} {D} {D'}
            {F : functor C C'} (FF : disp_functor F D D')
            (x : C).

    Definition fiber_functor_data : functor_data D[{x}] D'[{F x}].
    Proof.
      use tpair.
      - apply (λ xx', FF xx').
      - intros xx' xx ff.
        apply (transportf _ (functor_id _ _ ) (♯ FF ff)).
    Defined.

    Lemma is_functor_fiber_functor : is_functor fiber_functor_data.
    Proof.
      split; unfold functor_idax, functor_compax; cbn.
      - intros.
        apply transportf_pathsinv0.
        apply pathsinv0. apply disp_functor_id.
      - intros.
        etrans. apply maponpaths. apply disp_functor_transportf.
        etrans. apply transport_f_f.
        etrans. apply maponpaths. apply disp_functor_comp.
        etrans. apply transport_f_f.
        apply pathsinv0.
        etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
        etrans. apply transport_f_f.
        apply maponpaths_2, homset_property.
    Qed.

    Definition fiber_functor : functor D[{x}] D'[{F x}]
      := ( _ ,, is_functor_fiber_functor).

  End fix_context.

  (* TODO: consider lemma organisation in this file *)

  Definition is_z_iso_fiber_from_is_z_iso_disp
             {C : category} {D : disp_cat C}
             {c : C} {d d' : D c} (ff : d -->[identity c] d')
             (Hff : is_z_iso_disp (identity_z_iso c) ff)
    : @is_z_isomorphism (fiber_category D c) _ _ ff.
  Proof.
    exists (pr1 Hff).
    use tpair; cbn.
    + set (H := pr2 (pr2 Hff)).
      etrans. apply maponpaths, H.
      etrans. apply transport_f_b.
      use (@maponpaths_2 _ _ _ _ _ (paths_refl _)).
      apply homset_property.
    + set (H := pr1 (pr2 Hff)).
      etrans. apply maponpaths, H.
      etrans. apply transport_f_b.
      use (@maponpaths_2 _ _ _ _ _ (paths_refl _)).
      apply homset_property.
  Qed.

  Definition fiber_nat_trans {C C' : category}
             {F : functor C C'}
             {D D'} {FF FF' : disp_functor F D D'}
             (α : disp_nat_trans (nat_trans_id F) FF FF')
             (c : C)
    : nat_trans (fiber_functor FF c) (fiber_functor FF' c).
  Proof.
    use tpair; simpl.
    - intro d. exact (α c d).
    - unfold is_nat_trans; intros d d' ff; simpl.
      set (αff := pr2 α _ _ _ _ _ ff); simpl in αff.
      cbn.
      etrans. apply maponpaths, mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply maponpaths, αff.
      etrans. apply transport_f_b.
      apply @pathsinv0.
      etrans. apply maponpaths, mor_disp_transportf_prewhisker.
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
  Defined.

  Lemma fiber_functor_ff
        {C C' : category} {D} {D'}
        {F : functor C C'} (FF : disp_functor F D D')
        (H : disp_functor_ff FF)
        (c : C)
    : fully_faithful (fiber_functor FF c).
  Proof.
    intros xx yy; cbn.
    set (XR := H _ _ xx yy (identity _ )).
    apply twooutof3c.
    - apply XR.
    - apply isweqtransportf.
  Defined.

End Fiber_Functors.

(**
 Fiber fucntor of the identity and the composition
 *)
Definition fiber_functor_identity
           {C : category}
           (D : disp_cat C)
           (x : C)
  : nat_z_iso
      (functor_identity _)
      (fiber_functor (disp_functor_identity D) x).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ _, identity _).
    + intros xx yy ff ; cbn.
      rewrite id_right_disp.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - intros xx.
    apply (@is_z_isomorphism_identity (fiber_category D x)).
Defined.

Definition fiber_functor_comp
           {C : category}
           {D₁ D₂ D₃ : disp_cat C}
           (F : disp_functor (functor_identity C) D₁ D₂)
           (G : disp_functor (functor_identity C) D₂ D₃)
           (x : C)
  : nat_z_iso
      (fiber_functor F x ∙ fiber_functor G x)
      (fiber_functor (disp_functor_over_id_composite F G) x).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ _, identity _).
    + intros xx yy ff ; cbn.
      rewrite id_right_disp.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - intros xx.
    apply (@is_z_isomorphism_identity (fiber_category _ x)).
Defined.

(**
   Note: the previous lemma only considers displayed functor over the identity
   whereas the next one is the more general case.
   Note that the previous lemma also uses a more specialized composition operation.
 *)
Definition fiber_functor_comp_nat_trans
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           (FF : disp_functor F D₁ D₂)
           (GG : disp_functor G D₂ D₃)
           (x : C₁)
  : fiber_functor FF x ∙ fiber_functor GG (F x)
    ⟹
    fiber_functor (disp_functor_composite FF GG) x.
Proof.
  use make_nat_trans.
  - exact (λ _, identity _).
  - abstract
      (intros xx yy ff ;
       refine (id_right _ @ _ @ !(id_left _)) ;
       cbn ;
       rewrite disp_functor_transportf ;
       rewrite transport_f_f ;
       apply idpath).
Defined.

Definition fiber_functor_comp_nat_z_iso
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           (FF : disp_functor F D₁ D₂)
           (GG : disp_functor G D₂ D₃)
           (x : C₁)
  : nat_z_iso
      (fiber_functor FF x ∙ fiber_functor GG (F x))
      (fiber_functor (disp_functor_composite FF GG) x).
Proof.
  use make_nat_z_iso.
  - exact (fiber_functor_comp_nat_trans FF GG x).
  - intro xx.
    apply is_z_isomorphism_identity.
Defined.
