(** ** Equivalence of categories

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)

*)


(** ** Contents:

- Definition of (adjoint) equivalence of categories [adj_equivalence_of_cats]
- Constructor for an equivalence of categories from a right adjoint functor
    [adj_equivalence_from_right_adjoint]
- Equivalence of categories yields weak equivalence of object types
    [weq_on_objects_from_adj_equiv_of_cats]
- A fully faithful and ess. surjective functor induces equivalence of precategories if it is also
    split ess. surjective or if the source is a univalent_category
    [rad_equivalence_of_cats'] [rad_equivalence_of_cats]

*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

(** * Sloppy equivalence of categories *)

Definition forms_equivalence {A B : category} (X : adjunction_data A B)
           (η := adjunit X) (ε := adjcounit X) : UU
  := (∏ a, is_z_isomorphism (η a)) × (∏ b, is_z_isomorphism (ε b)).

Definition make_forms_equivalence {A B : category}
           (adjData : adjunction_data A B)
           (η := adjunit adjData)
           (ε := adjcounit adjData)
           (η_iso : ∏(a : A), is_z_isomorphism (η a))
           (ε_iso : ∏(b : B), is_z_isomorphism (ε b)) : forms_equivalence adjData
    := (η_iso ,, ε_iso).

Definition equivalence_of_cats (A B : category) : UU
  := ∑ (X : adjunction_data A B), forms_equivalence X.

#[reversible=no] Coercion adjunction_data_from_equivalence_of_cats {A B}
         (X : equivalence_of_cats A B) : adjunction_data A B := pr1 X.

Definition make_equivalence_of_cats {A B : category}
           (adjData : adjunction_data A B)
           (eqvProp : forms_equivalence adjData) : equivalence_of_cats A B
  := (adjData ,, eqvProp).

Definition adjunitiso {A B : category} (X : equivalence_of_cats A B)
           (a : A) : z_iso a (right_functor X (left_functor X a)).
Proof.
  exists (adjunit X a).
  exact (pr1 (pr2 X) a).
Defined.

Definition adjcounitiso {A B : category} (X : equivalence_of_cats A B)
           (b : B) : z_iso (left_functor X (right_functor X b)) b.
Proof.
 exists (adjcounit X b).
 exact (pr2 (pr2 X) b).
Defined.

(** * Equivalence of (pre)categories *)

Definition adj_equivalence_of_cats {A B : category} (F : functor A B) : UU :=
   ∑ (H : is_left_adjoint F), forms_equivalence H.

Definition adj_from_equiv (D1 D2 : category) (F : functor D1 D2):
    adj_equivalence_of_cats F → is_left_adjoint F := λ x, pr1 x.
Coercion adj_from_equiv : adj_equivalence_of_cats >-> is_left_adjoint.

Definition make_adj_equivalence_of_cats {A B : category} (F : functor A B)
           (G : functor B A) η ε
           (H1 : form_adjunction F G η ε)
           (H2 : forms_equivalence ((F,,G,,η,,ε)))
  : adj_equivalence_of_cats F.
Proof.
  use tpair.
  - exists G. exists (η,,ε). apply H1.
  - apply H2.
Defined.

Section MakeAdjEquivalenceOfCats'.

  Context {A B : category}.
  Context (F : functor A B).
  Context (G : functor B A).
  Context (η : functor_identity B ⟹ G ∙ F).
  Context (ε : F ∙ G ⟹ functor_identity A).
  Context (H1 : form_adjunction G F η ε).
  Context (H2 : ∏ a, is_z_isomorphism (η a)).
  Context (H3 : ∏ a, is_z_isomorphism (ε a)).

  Definition make_adj_equivalence_of_cats'_unit_nat_trans_data
    : nat_trans_data (functor_identity A) (F ∙ G).
  Proof.
    intro a.
    exact (inv_from_z_iso (_ ,, H3 a)).
  Defined.

  Lemma make_adj_equivalence_of_cats'_unit_is_nat_trans
    : is_nat_trans _ _ make_adj_equivalence_of_cats'_unit_nat_trans_data.
  Proof.
    intros a a' f.
    symmetry.
    apply z_iso_inv_on_right.
    rewrite assoc.
    apply z_iso_inv_on_left.
    symmetry.
    apply nat_trans_ax.
  Qed.

  Definition make_adj_equivalence_of_cats'_unit
    : functor_identity A ⟹ F ∙ G
    := make_nat_trans _ _ _ make_adj_equivalence_of_cats'_unit_is_nat_trans.

  Definition make_adj_equivalence_of_cats'_counit_nat_trans_data
    : nat_trans_data (G ∙ F) (functor_identity B).
  Proof.
    intro a.
    exact (inv_from_z_iso (_ ,, H2 a)).
  Defined.

  Lemma make_adj_equivalence_of_cats'_counit_is_nat_trans
    : is_nat_trans _ _ make_adj_equivalence_of_cats'_counit_nat_trans_data.
  Proof.
    intros a a' f.
    symmetry.
    apply z_iso_inv_on_right.
    rewrite assoc.
    apply z_iso_inv_on_left.
    symmetry.
    apply nat_trans_ax.
  Qed.

  Definition make_adj_equivalence_of_cats'_counit
    : G ∙ F ⟹ functor_identity B
    := make_nat_trans _ _ _ make_adj_equivalence_of_cats'_counit_is_nat_trans.

  Lemma make_adj_equivalence_of_cats'_form_adjunction
    : form_adjunction F G make_adj_equivalence_of_cats'_unit make_adj_equivalence_of_cats'_counit.
  Proof.
    use make_form_adjunction.
    - intro a.
      refine (maponpaths (λ x, x · _) (functor_on_inv_from_z_iso _ _) @ _).
      apply z_iso_inv_on_right.
      symmetry.
      refine (id_right _ @ _).
      refine (_ @ id_right _).
      symmetry.
      apply z_iso_inv_on_right.
      symmetry.
      apply (pr2 H1).
    - intro a.
      refine (maponpaths _ (functor_on_inv_from_z_iso _ _) @ _).
      apply z_iso_inv_on_right.
      symmetry.
      refine (id_right _ @ _).
      refine (_ @ id_right _).
      symmetry.
      apply z_iso_inv_on_right.
      symmetry.
      apply (pr1 H1).
  Qed.

  Definition make_adj_equivalence_of_cats'_are_adjoints
    : are_adjoints F G
    := make_are_adjoints _ _
        make_adj_equivalence_of_cats'_unit
        make_adj_equivalence_of_cats'_counit
        make_adj_equivalence_of_cats'_form_adjunction.

  Lemma make_adj_equivalence_of_cats'_forms_equivalence
    : forms_equivalence (G ,, make_adj_equivalence_of_cats'_are_adjoints : is_left_adjoint F).
  Proof.
    split;
      intro;
      apply is_z_iso_inv_from_z_iso.
  Qed.

  Definition make_adj_equivalence_of_cats'
  : adj_equivalence_of_cats F.
  Proof.
    use tpair.
    - exists G.
      exact make_adj_equivalence_of_cats'_are_adjoints.
    - exact make_adj_equivalence_of_cats'_forms_equivalence.
  Defined.

End MakeAdjEquivalenceOfCats'.

Definition adj_equivalence_from_right_adjoint
  {A B : category}
  (F : functor A B)
  (H1 : is_right_adjoint F)
  (H2 : ∏ a, is_z_isomorphism ((unit_from_right_adjoint H1) a))
  (H3 : ∏ a, is_z_isomorphism ((counit_from_right_adjoint H1) a))
  : adj_equivalence_of_cats F
  := make_adj_equivalence_of_cats'
    F
    (left_adjoint H1)
    (unit_from_right_adjoint H1)
    (counit_from_right_adjoint H1)
    (pr2 (pr2 H1))
    H2
    H3.

Definition adj_equivalence_inv {A B : category}
  {F : functor A B} (HF : adj_equivalence_of_cats F) : functor B A :=
    right_adjoint HF.

Local Notation "HF ^^-1" := (adj_equivalence_inv  HF)(at level 3).

Section Accessors.
  Context {A B : category} {F : functor A B} (HF : adj_equivalence_of_cats F).

  Definition unit_pointwise_z_iso_from_adj_equivalence :
      ∏ a, z_iso a (HF^^-1 (F a)).
  Proof.
  intro a.
  exists (unit_from_left_adjoint HF a).
  exact (pr1 (pr2 HF) a).
  Defined.

  Definition counit_pointwise_z_iso_from_adj_equivalence :
      ∏ b, z_iso (F (HF^^-1 b)) b.
  Proof.
    intro b.
    exists (counit_from_left_adjoint HF b).
    exact (pr2 (pr2 HF) b).
  Defined.

  Definition unit_nat_z_iso_from_adj_equivalence_of_cats  :
    nat_z_iso (functor_identity A) (functor_composite F (right_adjoint HF)).
  Proof.
    exists (unit_from_left_adjoint HF).
    exact (dirprod_pr1 (pr2 HF)).
  Defined.

  Definition counit_nat_z_iso_from_adj_equivalence_of_cats :
    nat_z_iso (functor_composite (right_adjoint HF) F) (functor_identity B).
  Proof.
    exists (counit_from_left_adjoint HF).
    exact (dirprod_pr2 (pr2 HF)).
  Defined.

  Definition unit_z_iso_from_adj_equivalence_of_cats :
    z_iso (C:=[A, A]) (functor_identity A)
        (functor_composite F (right_adjoint HF)).
  Proof.
    exists (unit_from_left_adjoint HF).
    apply nat_trafo_z_iso_if_pointwise_z_iso. intro c.
    apply (pr1 (pr2 HF)).
  Defined.

  Definition counit_z_iso_from_adj_equivalence_of_cats :
    z_iso (C:=[B, B]) (functor_composite (right_adjoint HF) F)
        (functor_identity B).
  Proof.
    exists (counit_from_left_adjoint HF).
    apply nat_trafo_z_iso_if_pointwise_z_iso. intro c.
    apply (pr2 (pr2 HF)).
  Defined.
End Accessors.

Section Inverse.

  Context {A B : category}.
  Context (F : functor A B).
  Context (H : adj_equivalence_of_cats F).

  Definition adj_equivalence_of_cats_inv
    : adj_equivalence_of_cats (H^^-1)
    := adj_equivalence_from_right_adjoint
      (right_adjoint H)
      (is_right_adjoint_right_adjoint H)
      (pr1 (pr2 H))
      (pr2 (pr2 H)).

End Inverse.

Section AdjEquiv.
  Definition adj_equiv (A B : category) : UU
    := ∑ F : functor A B,
        adj_equivalence_of_cats F.

  #[reversible=no] Coercion left_adjequiv (A B : category)
           (F : adj_equiv A B) : functor A B := pr1 F.

  #[reversible=no] Coercion adj_equiv_of_cats_from_adj {A B : category}
           (E : adj_equiv A B) : adj_equivalence_of_cats E
    := pr2 E.

  #[reversible=no] Coercion adj_from_adj_equiv {A B} (F : adj_equiv A B) : adjunction A B.
  Proof.
    use make_adjunction.
    use(make_adjunction_data F).
    - exact(right_adjoint F).
    - exact(adjunit F).
    - exact(adjcounit F).
    - use make_form_adjunction.
      + apply triangle_id_left_ad.
      + apply triangle_id_right_ad.
  Defined.

  #[reversible=no] Coercion equiv_from_adj_equiv {A B} (F : adj_equiv A B) : equivalence_of_cats A B.
  Proof.
    use make_equivalence_of_cats.
    use(make_adjunction_data F).
    - exact(right_adjoint F).
    - exact(adjunit F).
    - exact(adjcounit F).
    - use make_forms_equivalence.
      + apply unit_pointwise_z_iso_from_adj_equivalence.
      + apply counit_pointwise_z_iso_from_adj_equivalence.
  Defined.
End AdjEquiv.

(** * Adjointification of a sloppy equivalence *)


(** ** One triangle equality is enough *)

(** Proof ported from Peter Lumsdaine's proof of the analog for displayed categories
    see UniMath/TypeTheory
*)
Lemma triangle_2_from_1 {C D}
  (A : adjunction_data C D)
  (E : forms_equivalence A)
: triangle_1_statement A -> triangle_2_statement A.
Proof.
  destruct A as [F [G [η ε]]].
  destruct E as [Hη Hε]; cbn in Hη, Hε.
  unfold triangle_1_statement, triangle_2_statement; cbn.
  intros T1 x.
  assert (etaH := nat_trans_ax η); cbn in etaH.
  assert (epsH := nat_trans_ax ε); cbn in epsH.

  (* Algebraically, this goes as follows:
  η G ; G ε
  = G ε^ ; η^ G ; η G ; G ε ; η G ; G ε          [by inverses, 1]
  = G ε^ ; η^ G ; η G ; η G F G ; G F G ε ; G ε  [by naturality, 2]
  = G ε^ ; η^ G ; η G ; η G F G ; G ε F G ; G ε  [by naturality, 3]
  = G ε^ ; η^ G ; η G ; G F η G ; G ε F G ; G ε  [by naturality, 4]
  = G ε^ ; η^ G ; η G ; G (F η ; ε F ) G ; G ε   [by functoriality, 5]
  = G ε^ ; η^ G ; η G ; G ε                      [by T1, 6]
  = 1                                            [by inverses, 7]
*)

  apply (invmaponpathsweq (make_weq _ (z_iso_comp_left_isweq (_,,Hη _ ) _ ))).
  cbn.
  apply pathsinv0. etrans. apply id_left. etrans. apply (! id_right _ ).
  apply pathsinv0.
  apply (z_iso_inv_to_left _ _ _  (_,,Hη _ )).
  apply (invmaponpathsweq (make_weq _ (z_iso_comp_left_isweq (functor_on_z_iso G (_,,Hε _ )) _ ))).
  cbn.
  set (XR' := functor_on_z_iso G (_,,Hε x)).
  cbn in XR'.
  apply pathsinv0. etrans. apply id_left. etrans. apply (! id_right _ ).
  apply pathsinv0.
  apply (z_iso_inv_to_left _ _  _ XR').
  unfold XR'; clear XR'.

  repeat rewrite assoc.
  set (i := inv_from_z_iso (functor_on_z_iso G (ε x ,, Hε x))).
  set (i' := inv_from_z_iso (η (G x) ,, Hη (G x))).
  etrans. apply cancel_postcomposition. repeat rewrite <- assoc.
          rewrite etaH. apply idpath.
  etrans. repeat rewrite <- assoc. rewrite <- functor_comp.
          rewrite (epsH). rewrite functor_comp. apply idpath.
  etrans. apply maponpaths. apply maponpaths. repeat rewrite assoc. rewrite etaH.
          apply cancel_postcomposition. rewrite <- assoc. rewrite <- functor_comp.
          rewrite T1. rewrite functor_id. apply id_right.
  etrans. apply maponpaths. rewrite assoc. apply cancel_postcomposition.
          use (z_iso_after_z_iso_inv (_ ,, Hη _ )).
  rewrite id_left.
  apply (z_iso_after_z_iso_inv ).
Defined.


(** ** Adjointification *)

Section adjointification.

Context {C D : category} (E : equivalence_of_cats C D).
Let F : functor C D := left_functor E.
Let G : functor D C := right_functor E.

Let ηntiso : z_iso (C:= [C,C]) (functor_identity _ ) (F ∙ G).
Proof.
  use z_iso_from_nat_z_iso.
  exists (adjunit E). intro c.
  apply (pr1 (pr2 E)).
Defined.

Let εntiso : z_iso (C:= [D,D]) (G ∙ F) (functor_identity _ ).
Proof.
  use z_iso_from_nat_z_iso.
  exists (adjcounit E). intro c.
  apply (pr2 (pr2 E)).
Defined.

Let FF : functor [D,D] [C, D]
  := (pre_comp_functor F).

Let GG : functor [C, D] [D, D]
  := (pre_comp_functor G).


Definition ε'ntiso : z_iso (C:= [D,D]) (G ∙ F) (functor_identity _ ).
Proof.
  eapply z_iso_comp.
    set (XR := functor_on_z_iso GG (functor_on_z_iso FF εntiso)).
    set (XR':= z_iso_inv_from_z_iso XR). apply XR'.
  eapply z_iso_comp.
     2: apply εntiso.
  set (XR := functor_on_z_iso (pre_comp_functor G) (z_iso_inv_from_z_iso ηntiso)).
  set (XR':= functor_on_z_iso (post_comp_functor F) XR).
  apply XR'.
Defined.


Definition adjointification_triangle_1
  : triangle_1_statement (F,,G,, pr1 ηntiso,, pr1 ε'ntiso).
Proof.
  intro x. cbn. repeat rewrite assoc.
  assert (ηinvH := nat_trans_ax (inv_from_z_iso ηntiso)).
  cbn in ηinvH. simpl in ηinvH.
  assert (εinvH := nat_trans_ax (inv_from_z_iso εntiso)).
  cbn in εinvH. simpl in εinvH.
  etrans. apply cancel_postcomposition. apply cancel_postcomposition.
          etrans. apply maponpaths. apply (! (id_right _ )).
          rewrite id_right. apply εinvH.
  repeat rewrite assoc. rewrite assoc4.
  apply id_conjugation.
  - etrans. eapply pathsinv0. apply functor_comp.
    etrans. apply maponpaths. etrans. apply maponpaths. eapply pathsinv0. apply id_right.
            rewrite id_right. apply ηinvH.
    etrans. apply maponpaths.
    apply (nat_trans_inv_pointwise_inv_before_z_iso _ _ _ _ _ ηntiso (pr2 ηntiso)).
    apply functor_id.
  - assert (XR := nat_trans_inv_pointwise_inv_before_z_iso _ _ _ _ _ εntiso (pr2 εntiso)).
    cbn in XR.
    etrans. apply cancel_postcomposition. eapply pathsinv0. apply id_right. rewrite id_right. apply XR.
Qed.

Lemma adjointification_forms_equivalence :
  forms_equivalence (F,, G,, pr1 ηntiso,, pr1 ε'ntiso).
Proof.
  split.
  - cbn. apply (nat_trafo_pointwise_z_iso_if_z_iso _ ηntiso (pr2 ηntiso)).
  - cbn. apply (nat_trafo_pointwise_z_iso_if_z_iso _ ε'ntiso (pr2 ε'ntiso)).
Qed.

Definition adjointification_triangle_2
  : triangle_2_statement (F,,G,,pr1 ηntiso,,pr1 ε'ntiso).
Proof.
  use triangle_2_from_1.
  - apply adjointification_forms_equivalence.
  - apply adjointification_triangle_1.
Qed.

Definition adjointification : adj_equivalence_of_cats F.
Proof.
  use make_adj_equivalence_of_cats.
  - exact G.
  - apply ηntiso.
  - apply ε'ntiso.
  - exists adjointification_triangle_1.
    apply adjointification_triangle_2.
  - apply adjointification_forms_equivalence.
Defined.

End adjointification.

(** * Identity functor is an adjoint equivalence *)

Lemma identity_functor_is_adj_equivalence {A : category} :
  adj_equivalence_of_cats (functor_identity A).
Proof.
  use tpair.
  - exact is_left_adjoint_functor_identity.
  - now split; intros a; apply identity_is_z_iso.
Defined.

(** * Equivalence of categories yields equivalence of object types *)
(**  Fundamentally needed that both source and target are categories *)

Lemma adj_equiv_of_cats_is_weq_of_objects (A B : category)
   (HA : is_univalent A) (HB : is_univalent B) (F : [A, B])
   (HF : adj_equivalence_of_cats F) : isweq (pr1 (pr1 F)).
Proof.
  set (G := right_adjoint HF).
  set (et := unit_z_iso_from_adj_equivalence_of_cats HF).
  set (ep := counit_z_iso_from_adj_equivalence_of_cats HF).
  set (AAcat := is_univalent_functor_category A _ HA).
  set (BBcat := is_univalent_functor_category B _ HB).
  set (Et := isotoid _ AAcat et).
  set (Ep := isotoid _ BBcat ep).
  apply (isweq_iso _ (λ b, pr1 (right_adjoint HF) b)); intro a.
  apply (!toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Et)) a).
  now apply (toforallpaths _ _ _ (base_paths _ _ (base_paths _ _ Ep))).
Defined.

Definition weq_on_objects_from_adj_equiv_of_cats (A B : category)
   (HA : is_univalent A) (HB : is_univalent B) (F : ob [A, B])
   (HF : adj_equivalence_of_cats F) : weq
          (ob A) (ob B).
Proof.
  exists (pr1 (pr1 F)).
  now apply (@adj_equiv_of_cats_is_weq_of_objects _ _  HA).
Defined.


(** If the source precategory is a univalent_category, then being split
    essentially surjective is a proposition *)

Lemma isaprop_sigma_z_iso (A B : category) (HA : is_univalent A)
     (F : functor A B) (HF : fully_faithful F) :
     ∏ b : ob B, isaprop (∑ a : ob A, z_iso (F a) b).
Proof.
  intro b.
  apply invproofirrelevance.
  intros x x'; destruct x as [a f]; destruct x' as [a' f'].
  set (fminusf := z_iso_comp f (z_iso_inv_from_z_iso f')).
  set (g := iso_from_fully_faithful_reflection HF fminusf).
  apply (two_arg_paths_f (B:=λ a', z_iso (F a') b) (isotoid _ HA g)).
  intermediate_path (z_iso_comp (z_iso_inv_from_z_iso
    (functor_on_z_iso F (idtoiso (isotoid _ HA g)))) f).
  - generalize (isotoid _ HA g).
    intro p0; destruct p0.
    rewrite <- functor_on_z_iso_inv. simpl.
    rewrite z_iso_inv_of_z_iso_id.
    apply z_iso_eq.
    simpl; rewrite functor_id.
    rewrite id_left.
    apply idpath.
  - rewrite idtoiso_isotoid.
    unfold g; clear g.
    unfold fminusf; clear fminusf.
    assert (HFg : functor_on_z_iso F
          (iso_from_fully_faithful_reflection HF
            (z_iso_comp f (z_iso_inv_from_z_iso f'))) =
            z_iso_comp f (z_iso_inv_from_z_iso f')).
    + generalize (z_iso_comp f (z_iso_inv_from_z_iso f')).
      intro h.
      apply z_iso_eq; simpl.
      set (H3:= homotweqinvweq (weq_from_fully_faithful HF a a')).
      simpl in H3. unfold fully_faithful_inv_hom.
      unfold invweq; simpl.
      rewrite H3; apply idpath.
    + rewrite HFg.
      rewrite z_iso_inv_of_z_iso_comp.
      apply z_iso_eq; simpl.
      repeat rewrite <- assoc.
      rewrite z_iso_after_z_iso_inv.
      rewrite id_right.
      set (H := z_iso_inv_z_iso_inv _ _ f').
      now apply (base_paths _ _ H).
Qed.

Lemma isaprop_split_essentially_surjective (A B : category) (HA : is_univalent A)
      (F : functor A B) (HF : fully_faithful F) :
  isaprop (split_essentially_surjective F).
Proof.
  apply impred; intro.
  now apply isaprop_sigma_z_iso.
Qed.

(** If the source precategory is a univalent_category, then essential
    surjectivity of a fully faithful functor implies split essential
    surjectivity. *)
Lemma ff_essentially_surjective_to_split (A B : category) (HA : is_univalent A)
      (F : functor A B) (HF : fully_faithful F) (HF' : essentially_surjective F) :
  split_essentially_surjective F.
Proof.
  intro b.
  apply (squash_to_prop (HF' b)).
  - apply isaprop_sigma_z_iso; assumption.
  - exact (idfun _).
Defined.

(** * From full faithfullness and ess surj to equivalence *)

(** A fully faithful and ess. surjective functor induces an
   equivalence of precategories, if the source is a
    univalent_category.
*)

Section FullyFaithfulAndSplitEssentiallySurjectiveToEquivalence.

Variables A B : category.
Variable F : functor A B.
Hypothesis HF : fully_faithful F.
Hypothesis HS : split_essentially_surjective F.

(** Definition of a functor which will later be the right adjoint. *)

Definition rad_ob
  : ob B -> ob A
  := split_essentially_surjective_inv_on_obj F HS.

(** Definition of the epsilon transformation *)

Definition rad_eps (b : ob B) : z_iso (F (rad_ob b)) b := pr2 (HS _).

(** The right adjoint on morphisms *)

Definition rad_mor (b b' : ob B) (g : b --> b') : rad_ob b --> rad_ob b'.
Proof.
  set (epsgebs' := rad_eps b · g · z_iso_inv_from_z_iso (rad_eps b')).
  exact (fully_faithful_inv_hom HF (rad_ob b) _ epsgebs').
Defined.

(** Definition of the eta transformation *)

Definition rad_eta (a : ob A) : a --> rad_ob (F a).
Proof.
  set (epsFa := inv_from_z_iso (rad_eps (F a))).
  exact (fully_faithful_inv_hom HF _ _ epsFa).
Defined.

(** Above data specifies a functor *)

Definition rad_functor_data
  : functor_data B A
  := make_functor_data rad_ob rad_mor.

Lemma rad_is_functor : is_functor rad_functor_data.
Proof.
  split. simpl.
  intro b. simpl. unfold rad_mor. simpl.
  rewrite id_right, z_iso_inv_after_z_iso, fully_faithful_inv_identity.
  apply idpath.

  intros a b c f g. simpl.
  unfold rad_mor; simpl.
  rewrite <- fully_faithful_inv_comp.
  apply maponpaths.
  repeat rewrite <- assoc.
  repeat apply maponpaths.
  rewrite assoc.
  rewrite z_iso_after_z_iso_inv, id_left.
  apply idpath.
Qed.

Definition rad : ob [B, A]
  := make_functor rad_functor_data rad_is_functor.

(** Epsilon is natural *)

Lemma rad_eps_is_nat_trans : is_nat_trans
    (functor_composite rad F) (functor_identity B)
       (λ b, rad_eps b).
Proof.
  unfold is_nat_trans.
  simpl.
  intros b b' g.
  unfold rad_mor; unfold fully_faithful_inv_hom.
  set (H3 := homotweqinvweq (weq_from_fully_faithful HF (pr1 rad b) (pr1 rad b'))).
  simpl in *.
  rewrite H3; clear H3.
  repeat rewrite <- assoc.
  rewrite z_iso_after_z_iso_inv, id_right.
  apply idpath.
Qed.

Definition rad_eps_trans : nat_trans _ _ :=
  make_nat_trans _ _ _ rad_eps_is_nat_trans.

(** Eta is natural *)

Ltac inv_functor x y :=
   let H:=fresh in
   set (H:= homotweqinvweq (weq_from_fully_faithful HF x y));
     simpl in H;
     unfold fully_faithful_inv_hom; simpl;
     rewrite H; clear H.

Lemma rad_eta_is_nat_trans : is_nat_trans
         (functor_identity A) (functor_composite F rad)
       (λ a, rad_eta a).
Proof.
  unfold is_nat_trans.
  simpl.
  intros a a' f.
  unfold rad_mor. simpl.
  apply (invmaponpathsweq
          (weq_from_fully_faithful HF a (rad_ob (F a')))).
  simpl; repeat rewrite functor_comp.
  unfold rad_eta.
  set (HHH := rad_eps_is_nat_trans (F a) (F a')).
  simpl in HHH; rewrite <- HHH; clear HHH.
  inv_functor a' (rad_ob (F a')).
  inv_functor a (rad_ob (F a)).
  inv_functor (rad_ob (F a)) (rad_ob (F a')).
  unfold rad_mor. simpl.
  repeat rewrite <- assoc.
  rewrite z_iso_inv_after_z_iso.
  rewrite id_right.
  inv_functor (rad_ob (F a)) (rad_ob (F a')).
  repeat rewrite assoc.
  rewrite z_iso_after_z_iso_inv.
  rewrite id_left.
  apply idpath.
Qed.

Definition rad_eta_trans : nat_trans _ _ :=
   tpair (is_nat_trans _ _ ) _ rad_eta_is_nat_trans.


(** The data [rad], [eta], [eps] forms an adjunction *)

Lemma rad_form_adjunction : form_adjunction F rad rad_eta_trans rad_eps_trans.
Proof.
  split; simpl.
  - intro a. cbn.
    unfold rad_eta.
    inv_functor a (rad_ob (F a)).
    apply z_iso_after_z_iso_inv.
  - intro b.
    apply (invmaponpathsweq
             (weq_from_fully_faithful HF (rad_ob b) (rad_ob b))).
    simpl; rewrite functor_comp.
    unfold rad_eta.
    inv_functor (rad_ob b) (rad_ob (F (rad_ob b))).
    unfold rad_mor.
    inv_functor (rad_ob (F (rad_ob b))) (rad_ob b).
    repeat rewrite assoc.
    rewrite z_iso_after_z_iso_inv.
    rewrite <- assoc.
    rewrite z_iso_inv_after_z_iso.
    rewrite id_left.
    rewrite functor_id.
    apply idpath.
Qed.

Definition rad_are_adjoints : are_adjoints F rad.
Proof.
  exists (make_dirprod rad_eta_trans rad_eps_trans).
  apply rad_form_adjunction.
Defined.

Definition rad_is_left_adjoint : is_left_adjoint F.
Proof.
  exists rad.
  apply rad_are_adjoints.
Defined.

(** Get an equivalence of precategories:

    remains to show that [eta], [eps] are isos
*)

Lemma rad_equivalence_of_cats' : adj_equivalence_of_cats F.
Proof.
  exists rad_is_left_adjoint.
  split; simpl.
  intro a.
  unfold rad_eta.
  set (H := fully_faithful_reflects_iso_proof _ _ _ HF
       a (rad_ob (F a))).
  simpl in *.
  set (H' := H (z_iso_inv_from_z_iso (rad_eps (F a)))).
  change ((fully_faithful_inv_hom HF a (rad_ob (F a))
     (inv_from_z_iso (rad_eps (F a))))) with
      (fully_faithful_inv_hom HF a (rad_ob (F a))
     (z_iso_inv_from_z_iso (rad_eps (F a)))).
  apply H'.
  intro b. apply (pr2 (rad_eps b)).
Defined.

End FullyFaithfulAndSplitEssentiallySurjectiveToEquivalence.

Lemma rad_equivalence_of_cats
  (A B : category)
  (HA : is_univalent A)
  (F : functor A B)
  (HF : fully_faithful F)
  (HS : essentially_surjective F)
 : adj_equivalence_of_cats F.
Proof.
  apply rad_equivalence_of_cats'.
  - exact HF.
  - apply ff_essentially_surjective_to_split;
    assumption.
Defined.
