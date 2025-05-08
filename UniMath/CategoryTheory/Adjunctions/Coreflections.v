(**************************************************************************************************

  Co-reflections

  A coreflection of an object d : D along a functor F : C → D, or equivalently a 'universal arrow'
  from F to d, consists of an object c : C, together with a morphism f : F c → d, such that every
  f': F c' → d factors uniquely as f' = # F g ⋅ f.
  Coreflections are very useful for formalizing, because one can use them to construct a right
  adjoint to a functor (Theorem 2 (iv) of Chapter IV.1 of MacLane).

  This file is the dual of Reflections.v

  Contents
  1. Coreflections with their constructors and accessors [coreflection]
  2. Some simple constructions
    [coreflection_data_precompose] [coreflection_data_postcompose]
    [identity_coreflection_data] [coreflection_arrow_eq]
  3. Coreflections are unique
  3.1. The isomorphism between two coreflections [coreflection_uniqueness_iso]
  3.2. The type of coreflections becomes a proposition in a univalent category
    [isaprop_coreflection]
  4. Having a right adjoint to a functor F is equivalent to having coreflections of every d along F
  4.1. The construction of coreflections from a right adjoint [right_adjoint_to_coreflection]
  4.2. The construction of a right adjoint from coreflections [coreflections_to_is_left_adjoint]
  4.3. The equivalence [right_adjoint_weq_coreflections]
  4.4. The interaction between [right_adjoint_weq_coreflections] and [φ_adj]
    [coreflections_to_are_adjoints_φ_adj]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.

Local Open Scope cat.

(** *  1. Coreflections with their constructors and accessors *)

Section Coreflections.

  Context {C D : category}.

  Definition coreflection_data
    (d : D)
    (F : C ⟶ D)
    : UU
    := ∑ (c : C), F c --> d.

  Definition make_coreflection_data
    {d : D}
    {F : C ⟶ D}
    (c : C)
    (f : F c --> d)
    : coreflection_data d F
    := c ,, f.

  Definition coreflection_data_object
    {d : D}
    {F : C ⟶ D}
    (f : coreflection_data d F)
    : C
    := pr1 f.

  Coercion coreflection_data_arrow
    {d : D}
    {F : C ⟶ D}
    (f : coreflection_data d F)
    : F (coreflection_data_object f) --> d
    := pr2 f.

  Definition is_coreflection
    {d : D}
    {F : C ⟶ D}
    (f : coreflection_data d F)
    : UU
    := ∏ (f' : coreflection_data d F),
        ∃! g, (f' : _ --> _) = # F g · f.

  Definition make_coreflection_arrow
    {d : D}
    {F : C ⟶ D}
    {f f' : coreflection_data d F}
    (g : coreflection_data_object f' --> coreflection_data_object f)
    (Hg : (f' : _ --> _) = # F g · f)
    (H : ∏ g' (H : (f' : _ --> _) = # F g' · f), g' = g)
    : ∃! g', (f' : _ --> _) = # F g' · f.
  Proof.
    use unique_exists.
    - exact g.
    - exact Hg.
    - abstract (
        intro g';
        apply homset_property
      ).
    - exact H.
  Defined.

  Lemma isaprop_is_coreflection
    {d : D}
    {F : C ⟶ D}
    (f : coreflection_data d F)
    : isaprop (is_coreflection f).
  Proof.
    apply impred_isaprop.
    intro.
    apply isapropiscontr.
  Qed.

  Definition coreflection
    (d : D)
    (F : C ⟶ D)
    : UU
    := ∑ (f : coreflection_data d F), is_coreflection f.

  Definition make_coreflection
    {d : D}
    {F : C ⟶ D}
    (f : coreflection_data d F)
    (H : is_coreflection f)
    : coreflection d F
    := f ,, H.

  Coercion coreflection_to_coreflection_data
    {d : D}
    {F : C ⟶ D}
    (f : coreflection d F)
    : coreflection_data d F
    := pr1 f.

  Definition coreflection_arrow
    {d : D}
    {F : C ⟶ D}
    (f : coreflection d F)
    (f' : coreflection_data d F)
    : coreflection_data_object f' --> coreflection_data_object f
    := pr1 (iscontrpr1 (pr2 f f')).

  Definition coreflection_arrow_commutes
    {d : D}
    {F : C ⟶ D}
    (f : coreflection d F)
    (f' : coreflection_data d F)
    : (f' : _ --> _) = # F (coreflection_arrow f f') · f
    := pr2 (iscontrpr1 (pr2 f f')).

  Definition coreflection_arrow_unique
    {d : D}
    {F : C ⟶ D}
    (f : coreflection d F)
    (f' : coreflection_data d F)
    (g : coreflection_data_object f' --> coreflection_data_object f)
    (Hg : (f' : _ --> _) = # F g · f)
    : g = coreflection_arrow f f'
    := path_to_ctr _ _ (pr2 f f') g Hg.

(** *  2. Some simple constructions *)

  Definition coreflection_data_precompose
    {c : C}
    {d : D}
    {F : C ⟶ D}
    (f : coreflection_data d F)
    (g : c --> coreflection_data_object f)
    : coreflection_data d F.
  Proof.
    use make_coreflection_data.
    - exact c.
    - exact (# F g · f).
  Defined.

  Definition coreflection_data_postcompose
    {c d : D}
    {F : C ⟶ D}
    (f : coreflection_data d F)
    (g : d --> c)
    : coreflection_data c F.
  Proof.
    use make_coreflection_data.
    - exact (coreflection_data_object f).
    - exact (f · g).
  Defined.

  Definition identity_coreflection_data
    (c : C)
    (F : C ⟶ D)
    : coreflection_data (F c) F
    := make_coreflection_data
      c
      (identity (F c)).

  Lemma coreflection_arrow_eq
    {d : D}
    {F : C ⟶ D}
    (f : coreflection d F)
    (f' : coreflection_data d F)
    (g g' : coreflection_data_object f' --> coreflection_data_object f)
    (H : # F g · f = # F g' · f)
    : g = g'.
  Proof.
    refine (coreflection_arrow_unique f (coreflection_data_precompose f g') _ (!H) @ !_).
    refine (coreflection_arrow_unique f (coreflection_data_precompose f g) _ H @ !_).
    unfold coreflection_data_precompose.
    now induction H.
  Qed.

(** *  3. Coreflections are unique *)
(** **  3.1. The isomorphism between two coreflections *)

  Definition coreflection_arrow_id
    {d : D}
    {F : C ⟶ D}
    (f f' : coreflection d F)
    : coreflection_arrow f f' · coreflection_arrow f' f = identity _.
  Proof.
    apply coreflection_arrow_eq.
    refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths _ (!coreflection_arrow_commutes _ _) @ _).
    refine (!coreflection_arrow_commutes _ _ @ !_).
    refine (maponpaths (λ x, x · _) (functor_id _ _) @ _).
    apply id_left.
  Qed.

  Definition coreflection_uniqueness_iso
    {d : D}
    {F : C ⟶ D}
    (f f' : coreflection d F)
    : z_iso (coreflection_data_object f) (coreflection_data_object f').
  Proof.
    use make_z_iso.
    - apply coreflection_arrow.
    - apply coreflection_arrow.
    - abstract (
        apply make_is_inverse_in_precat;
        apply coreflection_arrow_id
      ).
  Defined.

  Lemma coreflection_uniqueness_iso_commutes
    {d : D}
    {F : C ⟶ D}
    (f f' : coreflection d F)
    : # F (inv_from_z_iso (coreflection_uniqueness_iso f f')) · f = f'.
  Proof.
    exact (!coreflection_arrow_commutes f f').
  Qed.

(** **  3.2. The type of coreflections becomes a proposition in a univalent category *)

  Lemma coreflection_isotoid
    {d : D}
    {F : C ⟶ D}
    (HC : is_univalent C)
    (f f' : coreflection d F)
    (g : z_iso (coreflection_data_object f) (coreflection_data_object f'))
    (H : # F (inv_from_z_iso g) · f = f')
    : f = f'.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_coreflection.
    }
    use total2_paths_f.
    - use (isotoid _ HC).
      apply g.
    - refine (transportf_functor_isotoid _ _ _ _ @ _).
      exact H.
  Qed.

  Lemma isaprop_coreflection
    {d : D}
    {F : C ⟶ D}
    (HC : is_univalent C)
    (f f' : coreflection d F)
    : f = f'.
  Proof.
    use (coreflection_isotoid HC).
    - apply coreflection_uniqueness_iso.
    - apply coreflection_uniqueness_iso_commutes.
  Qed.

End Coreflections.

(** *  4. Having a right adjoint to a functor F is equivalent to having coreflections of every d along F *)
(** **  4.1. The construction of coreflections from a right adjoint *)

Definition right_adjoint_to_coreflection
  {X A : category}
  {F : X ⟶ A}
  (G : is_left_adjoint F)
  (a : A)
  : coreflection a F.
Proof.
  use make_coreflection.
  - use make_coreflection_data.
    + exact (right_adjoint G a).
    + exact (counit_from_left_adjoint G a).
  - intro f.
    use make_coreflection_arrow.
    + exact (adjunction_hom_weq (pr2 G) _ _ f).
    + abstract (
        refine (_ @ !maponpaths (λ x, x · _) (functor_comp _ _ _));
        refine (_ @ assoc _ _ _);
        refine (_ @ !maponpaths _ (nat_trans_ax (counit_from_left_adjoint G) _ _ _));
        refine (_ @ assoc' _ _ _);
        refine (_ @ !maponpaths (λ x, x · _) (triangle_id_left_ad (pr2 G) _));
        exact (!id_left _)
      ).
    + abstract (
        intros g Hg;
        apply switch_weq';
        exact (!Hg)
      ).
Defined.

(** **  4.2. The construction of a right adjoint from coreflections *)

Section CoreflectionsTorightAdjoint.

  Context {X A : category}.
  Context {F : functor A X}.
  Context (G0 : ∏ x, coreflection x F).

  Definition coreflections_to_functor_data : functor_data X A.
  Proof.
    use make_functor_data.
    - intro x.
      exact (coreflection_data_object (G0 x)).
    - intros a b f.
      exact (coreflection_arrow (G0 b) (coreflection_data_postcompose (G0 a) f)).
  Defined.

  Definition coreflections_to_is_functor : is_functor coreflections_to_functor_data.
  Proof.
    split.
    - intro x.
      refine (!coreflection_arrow_unique _ (coreflection_data_postcompose _ _) _ _).
      refine (id_right _ @ !_).
      refine (maponpaths (λ x, x · _) (functor_id _ _) @ _).
      apply id_left.
    - intros a b c f g.
      refine (!coreflection_arrow_unique _ (coreflection_data_postcompose _ _) _ _).
      refine (_ @ !maponpaths (λ x, x · _) (functor_comp _ _ _)).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths _ (coreflection_arrow_commutes (G0 c) (coreflection_data_postcompose _ _))).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ x, x · _) (coreflection_arrow_commutes (G0 b) (coreflection_data_postcompose _ _))).
      apply assoc.
  Qed.

  Definition coreflections_to_functor
    : functor X A
    := make_functor coreflections_to_functor_data coreflections_to_is_functor.

  Local Notation G
    := coreflections_to_functor.

  Definition coreflections_to_unit_data
    : nat_trans_data (functor_identity A) (F ∙ G)
    := λ a, coreflection_arrow (G0 _) (identity_coreflection_data _ _).

  Lemma coreflections_to_is_unit
    : is_nat_trans _ _ coreflections_to_unit_data.
  Proof.
    intros a b f.
    apply (coreflection_arrow_eq _ (coreflection_data_postcompose (identity_coreflection_data _ _) (# F f))).
    do 2 refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ !_).
    do 2 refine (assoc' _ _ _ @ !_).
    cbn.
    unfold coreflections_to_unit_data.
    cbn.
    refine (!maponpaths _ (coreflection_arrow_commutes _ (identity_coreflection_data b F)) @ _).
    refine (id_right _ @ !_).
    refine (!maponpaths _ (coreflection_arrow_commutes _ (coreflection_data_postcompose _ _)) @ _).
    refine (assoc _ _ _ @ _).
    refine (!maponpaths (λ x, x · _) (coreflection_arrow_commutes _ (identity_coreflection_data _ _)) @ _).
    apply id_left.
  Qed.

  Definition coreflections_to_unit
    : functor_identity A ⟹ F ∙ G
    := make_nat_trans _ _
      coreflections_to_unit_data
      coreflections_to_is_unit.

  Definition coreflections_to_counit
    : G ∙ F ⟹ functor_identity X.
  Proof.
    use make_nat_trans.
    - intro x.
      exact (G0 x).
    - abstract (
        intros a b f;
        exact (!coreflection_arrow_commutes (G0 b) (coreflection_data_postcompose (G0 a) f))
      ).
  Defined.

  Lemma coreflections_to_form_adjunction
    : form_adjunction F G coreflections_to_unit coreflections_to_counit.
  Proof.
    use make_form_adjunction.
    - intro a.
      exact (!coreflection_arrow_commutes (G0 _) (identity_coreflection_data _ _)).
    - intro x.
      apply (coreflection_arrow_eq (G0 x) (G0 x)).
      refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
      refine (assoc' _ _ _ @ _).
      refine (!maponpaths _ (coreflection_arrow_commutes _ (coreflection_data_postcompose _ _)) @ _).
      refine (assoc _ _ _ @ _).
      refine (!maponpaths (λ x, x · _) (coreflection_arrow_commutes _ (identity_coreflection_data _ _)) @ _).
      refine (_ @ !maponpaths (λ x, x · _) (functor_id _ _)).
      refine (_ @ !id_left _).
      apply id_left.
  Qed.

  Definition coreflections_to_are_adjoints
    : are_adjoints F G
    := make_are_adjoints _ _ _ _ coreflections_to_form_adjunction.

  Definition coreflections_to_is_left_adjoint
    : is_left_adjoint F
    := coreflections_to_are_adjoints.

  Definition coreflections_to_is_right_adjoint
    : is_right_adjoint G
    := coreflections_to_are_adjoints.

End CoreflectionsTorightAdjoint.

(** **  4.3. The equivalence *)

Definition right_adjoint_to_coreflections_to_right_adjoint
  {X A : category}
  {F : functor A X}
  (G : is_left_adjoint F)
  : coreflections_to_is_left_adjoint (right_adjoint_to_coreflection G) = G.
Proof.
  use total2_paths_f.
  - apply (functor_eq _ _ (homset_property _)).
    apply (maponpaths (make_functor_data _)).
    apply funextsec.
    intro a.
    apply funextsec.
    intro b.
    apply funextfun.
    intro f.
    refine (φ_adj_natural_postcomp (pr2 G) _ _ _ _ _ @ _).
    refine (maponpaths (λ x, x · _) (triangle_id_right_ad (pr2 G) _) @ _).
    apply id_left.
  - use subtypePath.
    {
      intro.
      apply isaprop_form_adjunction.
    }
    refine (pr1_transportf (B := λ _, _ × _) (P := λ x y, form_adjunction _ x (pr1 y) (pr2 y)) _ _ @ _).
    refine (transportf_dirprod (X ⟶ A) _ _ (_ ,, _) (pr1 G ,, pr12 G) _ @ _).
    use pathsdirprod;
      apply nat_trans_eq_alt;
      intro x;
    [ refine (eqtohomot (pr1_transportf (B := λ y, nat_trans_data _ (F ∙ y)) _ _) x @ _);
      refine (eqtohomot (functtransportf (λ (G' : X ⟶ A), (G' : _ → _)) (λ G', ∏ y, y --> G' (F y)) _ _) _ @ _);
      refine (!helper_A (λ x1 x0, x1 --> x0 (F x1)) _ _ x @ _);
      refine (maponpaths (λ x, _ (_ · x)) (functor_id (right_adjoint G) _) @ _);
      refine (maponpaths _ (id_right _) @ _);
      refine (transportf (λ e, transportf (λ y, x --> y (F x)) e _ = unit_from_left_adjoint G x) (_ : idpath _ = _) (idpath _))
    | refine (eqtohomot (pr1_transportf (B := λ y, nat_trans_data (y ∙ F) _) _ _) x @ _);
      refine (eqtohomot (functtransportf (λ (G' : X ⟶ A), (G' : _ → _)) (λ G', ∏ y, F (G' y) --> y) _ _) _ @ _);
      refine (!helper_A (λ y G', F (G' y) --> y) _ _ x @ _);
      refine (transportf (λ e, transportf (λ y, F (y x) --> x) e _ = counit_from_left_adjoint G x) (_ : idpath _ = _) (idpath _)) ];
      refine (!_ @ maponpathscomp (functor_data_from_functor X A) _ (functor_eq _ _ _ (pr1 (coreflections_to_is_left_adjoint (right_adjoint_to_coreflection G))) _ _));
      refine (maponpaths _ (total2_paths2_comp1 _ _) @ _);
      refine (maponpathscomp (λ x, make_functor_data _ x) _ _ @ _);
      apply maponpaths_for_constant_function.
Qed.

Lemma coreflections_to_right_adjoint_to_coreflections
  {X A : category}
  {G : functor A X}
  (F0 : ∏ x, coreflection x G)
  : right_adjoint_to_coreflection (coreflections_to_is_left_adjoint F0) = F0.
Proof.
  apply funextsec.
  intro x.
  use subtypePath.
  {
    intro.
    apply isaprop_is_coreflection.
  }
  reflexivity.
Qed.

Definition right_adjoint_weq_coreflections
  {X A : category}
  (G : functor A X)
  : is_left_adjoint G ≃ ∏ x, coreflection x G.
Proof.
  use weq_iso.
  - exact right_adjoint_to_coreflection.
  - exact coreflections_to_is_left_adjoint.
  - apply right_adjoint_to_coreflections_to_right_adjoint.
  - apply coreflections_to_right_adjoint_to_coreflections.
Defined.

(** ** 4.4. The interaction between [right_adjoint_weq_coreflections] and [φ_adj] *)

(* Note that for f : X⟦x, G a⟧, we have φ_adj_inv Adj f = #F f · G0 a definitionally *)
Lemma coreflections_to_are_adjoints_φ_adj
  {X A : category}
  {F : functor X A}
  (G0 : ∏ a, coreflection a F)
  {a : A}
  {x : X}
  (f : A⟦F x, a⟧)
  : φ_adj (coreflections_to_are_adjoints G0) f
    = coreflection_arrow (G0 a) (make_coreflection_data x f).
Proof.
  refine (coreflection_arrow_unique _ (make_coreflection_data x f) _ (!_)).
  refine (maponpaths (λ x, x · _) (functor_comp _ _ _) @ _).
  refine (assoc' _ _ _ @ _).
  refine (!maponpaths _ (coreflection_arrow_commutes _ (coreflection_data_postcompose _ _)) @ _).
  refine (assoc _ _ _ @ _).
  refine (!maponpaths (λ x, x · _)
    (coreflection_arrow_commutes _ (identity_coreflection_data _ _)) @ _).
  apply id_left.
Qed.
