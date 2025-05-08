(**************************************************************************************************

  Reflections

  A reflection of an object d : D along a functor F : C → D, or equivalently a 'universal arrow'
  from d to F, consists of an object c : C, together with a morphism f : d → F c, such that every
  f': d → F c' factors uniquely as f' = f · # F g.
  Reflections are very useful for formalizing, because one can use them to construct a left adjoint
  to a functor (Theorem 2 (ii) of Chapter IV.1 of MacLane).

  This file is the dual of Coreflections.v

  Contents
  1. Reflections with their constructors and accessors [reflection]
  2. Some simple constructions
    [reflection_data_precompose] [reflection_data_postcompose]
    [identity_reflection_data] [reflection_arrow_eq]
  3. Reflections are unique
  3.1. The isomorphism between two reflections [reflection_uniqueness_iso]
  3.2. The type of reflections becomes a proposition in a univalent category [isaprop_reflection]
  4. Having a left adjoint to a functor F is equivalent to having reflections of every d along F
  4.1. The construction of reflections from a left adjoint [left_adjoint_to_reflection]
  4.2. The construction of a left adjoint from reflections [reflections_to_is_right_adjoint]
  4.3. The equivalence [left_adjoint_weq_reflections]
  4.4. The interaction between [left_adjoint_weq_reflections] and [φ_adj_inv]
    [reflections_to_are_adjoints_φ_adj_inv]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.

Local Open Scope cat.

(** *  1. Reflections with their constructors and accessors *)

Section Reflections.

  Context {C D : category}.

  Definition reflection_data
    (d : D)
    (F : C ⟶ D)
    : UU
    := ∑ (c : C), d --> F c.

  Definition make_reflection_data
    {d : D}
    {F : C ⟶ D}
    (c : C)
    (f : d --> F c)
    : reflection_data d F
    := c ,, f.

  Definition reflection_data_object
    {d : D}
    {F : C ⟶ D}
    (f : reflection_data d F)
    : C
    := pr1 f.

  Coercion reflection_data_arrow
    {d : D}
    {F : C ⟶ D}
    (f : reflection_data d F)
    : d --> F (reflection_data_object f)
    := pr2 f.

  Definition is_reflection
    {d : D}
    {F : C ⟶ D}
    (f : reflection_data d F)
    : UU
    := ∏ (f' : reflection_data d F),
        ∃! g, (f' : _ --> _) = f · # F g.

  Definition make_reflection_arrow
    {d : D}
    {F : C ⟶ D}
    {f f' : reflection_data d F}
    (g : reflection_data_object f --> reflection_data_object f')
    (Hg : (f' : _ --> _) = f · # F g)
    (H : ∏ g' (H : (f' : _ --> _) = f · # F g'), g' = g)
    : ∃! g', (f' : _ --> _) = f · # F g'.
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

  Lemma isaprop_is_reflection
    {d : D}
    {F : C ⟶ D}
    (f : reflection_data d F)
    : isaprop (is_reflection f).
  Proof.
    apply impred_isaprop.
    intro.
    apply isapropiscontr.
  Qed.

  Definition reflection
    (d : D)
    (F : C ⟶ D)
    : UU
    := ∑ (f : reflection_data d F), is_reflection f.

  Definition make_reflection
    {d : D}
    {F : C ⟶ D}
    (f : reflection_data d F)
    (H : is_reflection f)
    : reflection d F
    := f ,, H.

  Coercion reflection_to_reflection_data
    {d : D}
    {F : C ⟶ D}
    (f : reflection d F)
    : reflection_data d F
    := pr1 f.

  Definition reflection_arrow
    {d : D}
    {F : C ⟶ D}
    (f : reflection d F)
    (f' : reflection_data d F)
    : reflection_data_object f --> reflection_data_object f'
    := pr1 (iscontrpr1 (pr2 f f')).

  Definition reflection_arrow_commutes
    {d : D}
    {F : C ⟶ D}
    (f : reflection d F)
    (f' : reflection_data d F)
    : (f' : _ --> _) = f · # F (reflection_arrow f f')
    := pr2 (iscontrpr1 (pr2 f f')).

  Definition reflection_arrow_unique
    {d : D}
    {F : C ⟶ D}
    (f : reflection d F)
    (f' : reflection_data d F)
    (g : reflection_data_object f --> reflection_data_object f')
    (Hg : (f' : _ --> _) = f · # F g)
    : g = reflection_arrow f f'
    := path_to_ctr _ _ (pr2 f f') g Hg.

(** *  2. Some simple constructions *)

  Definition reflection_data_precompose
    {c d : D}
    {F : C ⟶ D}
    (f : c --> d)
    (g : reflection_data d F)
    : reflection_data c F.
  Proof.
    use make_reflection_data.
    - exact (reflection_data_object g).
    - exact (f · g).
  Defined.

  Definition reflection_data_postcompose
    {c : C}
    {d : D}
    {F : C ⟶ D}
    (f : reflection_data d F)
    (g : reflection_data_object f --> c)
    : reflection_data d F.
  Proof.
    use make_reflection_data.
    - exact c.
    - exact (f · # F g).
  Defined.

  Definition identity_reflection_data
    (c : C)
    (F : C ⟶ D)
    : reflection_data (F c) F
    := make_reflection_data
      c
      (identity (F c)).

  Lemma reflection_arrow_eq
    {d : D}
    {F : C ⟶ D}
    (f : reflection d F)
    (f' : reflection_data d F)
    (g g' : reflection_data_object f --> reflection_data_object f')
    (H : f · # F g = f · # F g')
    : g = g'.
  Proof.
    refine (reflection_arrow_unique f (reflection_data_postcompose f g') _ (!H) @ !_).
    refine (reflection_arrow_unique f (reflection_data_postcompose f g) _ H @ !_).
    unfold reflection_data_postcompose.
    now induction H.
  Qed.

(** *  3. Reflections are unique *)
(** **  3.1. The isomorphism between two reflections *)

  Definition reflection_arrow_id
    {d : D}
    {F : C ⟶ D}
    (f f' : reflection d F)
    : reflection_arrow f f' · reflection_arrow f' f = identity _.
  Proof.
    apply reflection_arrow_eq.
    refine (maponpaths _ (functor_comp _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ x, x · _) (!reflection_arrow_commutes _ _) @ _).
    refine (!reflection_arrow_commutes _ _ @ !_).
    refine (maponpaths _ (functor_id _ _) @ _).
    apply id_right.
  Qed.

  Definition reflection_uniqueness_iso
    {d : D}
    {F : C ⟶ D}
    (f f' : reflection d F)
    : z_iso (reflection_data_object f) (reflection_data_object f').
  Proof.
    use make_z_iso.
    - apply reflection_arrow.
    - apply reflection_arrow.
    - abstract (
        apply make_is_inverse_in_precat;
        apply reflection_arrow_id
      ).
  Defined.

  Lemma reflection_uniqueness_iso_commutes
    {d : D}
    {F : C ⟶ D}
    (f f' : reflection d F)
    : f · # F (reflection_uniqueness_iso f f') = f'.
  Proof.
    exact (!reflection_arrow_commutes f f').
  Qed.

(** **  3.2. The type of reflections becomes a proposition in a univalent category *)

  Lemma reflection_isotoid
    {d : D}
    {F : C ⟶ D}
    (HC : is_univalent C)
    (f f' : reflection d F)
    (g : z_iso (reflection_data_object f) (reflection_data_object f'))
    (H : f · # F g = f')
    : f = f'.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_reflection.
    }
    use total2_paths_f.
    - use (isotoid _ HC).
      apply g.
    - refine (transportf_functor_isotoid' _ _ _ _ @ _).
      exact H.
  Qed.

  Lemma isaprop_reflection
    {d : D}
    {F : C ⟶ D}
    (HC : is_univalent C)
    (f f' : reflection d F)
    : f = f'.
  Proof.
    use (reflection_isotoid HC).
    - apply reflection_uniqueness_iso.
    - apply reflection_uniqueness_iso_commutes.
  Qed.

End Reflections.

(** *  4. Having a left adjoint to a functor F is equivalent to having reflections of every d along F *)
(** **  4.1. The construction of reflections from a left adjoint *)

Definition left_adjoint_to_reflection
  {X A : category}
  {G : X ⟶ A}
  (F : is_right_adjoint G)
  (a : A)
  : reflection a G.
Proof.
  use make_reflection.
  - use make_reflection_data.
    + exact (left_adjoint F a).
    + exact (unit_from_right_adjoint F a).
  - intro f.
    use make_reflection_arrow.
    + exact (invmap (adjunction_hom_weq (pr2 F) _ _) f).
    + abstract (
        refine (_ @ !maponpaths _ (functor_comp _ _ _));
        refine (_ @ assoc' _ _ _);
        refine (_ @ maponpaths (λ x, x · _) (nat_trans_ax (unit_from_right_adjoint F) _ _ _));
        refine (_ @ assoc _ _ _);
        refine (_ @ !maponpaths _ (triangle_id_right_ad (pr2 F) _));
        exact (!id_right _)
      ).
    + abstract (
        intros g Hg;
        apply pathsweq1;
        exact (!Hg)
      ).
Defined.

(** **  4.2. The construction of a left adjoint from reflections *)

Section ReflectionsToLeftAdjoint.

  Context {X A : category}.
  Context {G : A ⟶ X}.
  Context (F0 : ∏ x, reflection x G).

  Definition reflections_to_functor_data : functor_data X A.
  Proof.
    use make_functor_data.
    - intro x.
      exact (reflection_data_object (F0 x)).
    - intros a b f.
      exact (reflection_arrow (F0 a) (reflection_data_precompose f (F0 b))).
  Defined.

  Definition reflections_to_is_functor : is_functor reflections_to_functor_data.
  Proof.
    split.
    - intro x.
      refine (!reflection_arrow_unique _ (reflection_data_precompose _ _) _ _).
      refine (id_left _ @ !_).
      refine (maponpaths _ (functor_id _ _) @ _).
      apply id_right.
    - intros a b c f g.
      refine (!reflection_arrow_unique _ (reflection_data_precompose _ _) _ _).
      refine (_ @ !maponpaths _ (functor_comp _ _ _)).
      refine (_ @ assoc' _ _ _).
      refine (_ @ maponpaths (λ x, x · _) (reflection_arrow_commutes (F0 a) (reflection_data_precompose _ _))).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths _ (reflection_arrow_commutes (F0 b) (reflection_data_precompose _ _))).
      apply assoc'.
  Qed.

  Definition reflections_to_functor
    : functor X A
    := make_functor reflections_to_functor_data reflections_to_is_functor.

  Local Notation F
    := reflections_to_functor.

  Definition reflections_to_unit
    : functor_identity X ⟹ F ∙ G.
  Proof.
    use make_nat_trans.
    - intro x.
      exact (F0 x).
    - abstract (
        intros a b f;
        exact (reflection_arrow_commutes (F0 a) (reflection_data_precompose f (F0 b)))
      ).
  Defined.

  Definition reflections_to_counit_data
    : nat_trans_data (G ∙ F) (functor_identity A)
    := λ a, reflection_arrow (F0 _) (identity_reflection_data _ _).

  Lemma reflections_to_is_counit
    : is_nat_trans _ _ reflections_to_counit_data.
  Proof.
    intros a b f.
    apply (reflection_arrow_eq _ (reflection_data_precompose (# G f) (identity_reflection_data _ _))).
    do 2 refine (maponpaths _ (functor_comp _ _ _) @ !_).
    do 2 refine (assoc _ _ _ @ !_).
    refine (!maponpaths (λ x, x · _) (reflection_arrow_commutes _ (reflection_data_precompose _ _)) @ _).
    refine (assoc' _ _ _ @ _).
    refine (!maponpaths _ (reflection_arrow_commutes _ (identity_reflection_data _ _)) @ _).
    refine (id_right _ @ !_).
    refine (!maponpaths (λ x, x · _) (reflection_arrow_commutes _ (identity_reflection_data a G)) @ _).
    apply id_left.
  Qed.

  Definition reflections_to_counit
    : G ∙ F ⟹ functor_identity A
    := make_nat_trans _ _
      reflections_to_counit_data
      reflections_to_is_counit.

  Lemma reflections_to_form_adjunction
    : form_adjunction F G reflections_to_unit reflections_to_counit.
  Proof.
    use make_form_adjunction.
    - intro x.
      apply (reflection_arrow_eq (F0 x) (F0 x)).
      refine (maponpaths _ (functor_comp _ _ _) @ _).
      refine (assoc _ _ _ @ _).
      refine (!maponpaths (λ x, x · _) (reflection_arrow_commutes _ (reflection_data_precompose _ _)) @ _).
      refine (assoc' _ _ _ @ _).
      refine (!maponpaths (λ x, _ · x) (reflection_arrow_commutes _ (identity_reflection_data _ _)) @ _).
      refine (_ @ !maponpaths _ (functor_id _ _)).
      refine (_ @ !id_right _).
      apply id_right.
    - intro a.
      exact (!reflection_arrow_commutes (F0 _) (identity_reflection_data _ _)).
  Qed.

  Definition reflections_to_are_adjoints
    : are_adjoints F G
    := make_are_adjoints _ _ _ _ reflections_to_form_adjunction.

  Definition reflections_to_is_right_adjoint
    : is_right_adjoint G
    := reflections_to_are_adjoints.

  Definition reflections_to_is_left_adjoint
    : is_left_adjoint F
    := reflections_to_are_adjoints.

End ReflectionsToLeftAdjoint.

(** **  4.3. The equivalence *)

Definition left_adjoint_to_reflections_to_left_adjoint
  {X A : category}
  {G : functor A X}
  (F : is_right_adjoint G)
  : reflections_to_is_right_adjoint (left_adjoint_to_reflection F) = F.
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
    refine (φ_adj_inv_natural_precomp (pr2 F) _ _ _ _ _ @ _).
    refine (maponpaths (λ x, _ · x) (triangle_id_left_ad (pr2 F) _) @ _).
    apply id_right.
  - use subtypePath.
    {
      intro.
      apply isaprop_form_adjunction.
    }
    refine (pr1_transportf (B := λ _, _ × _) (P := λ x y, form_adjunction x _ (pr1 y) (pr2 y)) _ _ @ _).
    refine (transportf_dirprod (X ⟶ A) _ _ (_ ,, _) (pr1 F ,, pr12 F) _ @ _).
    use pathsdirprod;
      apply nat_trans_eq_alt;
      intro x;
    [ refine (eqtohomot (pr1_transportf (B := λ y, nat_trans_data _ (y ∙ G)) _ _) x @ _);
      refine (eqtohomot (functtransportf (λ (F' : X ⟶ A), (F' : _ → _)) (λ F', ∏ y, y --> G (F' y)) _ _) _ @ _);
      refine (!helper_A (λ y F', y --> G (F' y)) _ _ x @ _);
      refine (transportf (λ e, transportf (λ y, x --> G (y x)) e _ = unit_from_right_adjoint F x) (_ : idpath _ = _) (idpath _))
    | refine (eqtohomot (pr1_transportf (B := λ y, nat_trans_data (G ∙ y) _) _ _) x @ _);
      refine (eqtohomot (functtransportf (λ (F' : X ⟶ A), (F' : _ → _)) (λ F', ∏ y, F' (G y) --> y) _ _) _ @ _);
      refine (!helper_A (λ x1 x0, x0 (G x1) --> x1) _ _ x @ _);
      refine (maponpaths (λ x, _ (x · _)) (functor_id _ _) @ _);
      refine (maponpaths _ (id_left _) @ _);
      refine (transportf (λ e, transportf (λ y, y (G x) --> x) e _ = counit_from_right_adjoint F x) (_ : idpath _ = _) (idpath _)) ];
      refine (!_ @ maponpathscomp (functor_data_from_functor X A) _ (functor_eq _ _ _ (pr1 (reflections_to_is_right_adjoint (left_adjoint_to_reflection F))) _ _));
      refine (maponpaths _ (total2_paths2_comp1 _ _) @ _);
      refine (maponpathscomp (λ x, make_functor_data _ x) _ _ @ _);
      apply maponpaths_for_constant_function.
Qed.

Lemma reflections_to_left_adjoint_to_reflections
  {X A : category}
  {G : functor A X}
  (F0 : ∏ x, reflection x G)
  : left_adjoint_to_reflection (reflections_to_is_right_adjoint F0) = F0.
Proof.
  apply funextsec.
  intro x.
  use subtypePath.
  {
    intro.
    apply isaprop_is_reflection.
  }
  reflexivity.
Qed.

Definition left_adjoint_weq_reflections
  {X A : category}
  (G : functor A X)
  : is_right_adjoint G ≃ ∏ x, reflection x G.
Proof.
  use weq_iso.
  - exact left_adjoint_to_reflection.
  - exact reflections_to_is_right_adjoint.
  - apply left_adjoint_to_reflections_to_left_adjoint.
  - apply reflections_to_left_adjoint_to_reflections.
Defined.

(** ** 4.4. The interaction between [left_adjoint_weq_reflections] and [φ_adj_inv] *)

(* Note that for f : A⟦F x, a⟧, we have φ_adj Adj f = F0 x · #G f definitionally *)
Lemma reflections_to_are_adjoints_φ_adj_inv
  {X A : category}
  {G : functor A X}
  (F0 : ∏ x, reflection x G)
  {x : X}
  {a : A}
  (f : X⟦x, G a⟧)
  : φ_adj_inv (reflections_to_are_adjoints F0) f
    = reflection_arrow (F0 x) (make_reflection_data a f).
Proof.
  refine (reflection_arrow_unique _ (make_reflection_data a f) _ (!_)).
  refine (maponpaths _ (functor_comp _ _ _) @ _).
  refine (assoc _ _ _ @ _).
  refine (!maponpaths (λ x, x · _)
    (reflection_arrow_commutes _ (reflection_data_precompose _ _)) @ _).
  refine (assoc' _ _ _ @ _).
  refine (!maponpaths _ (reflection_arrow_commutes _ (identity_reflection_data _ _)) @ _).
  apply id_right.
Qed.
