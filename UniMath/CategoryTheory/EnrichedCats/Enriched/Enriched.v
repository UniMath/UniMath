From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
(** * Enriched categories *)

(** ** Contents

 - Definition
 - Enriched functors
  - Composition of enriched functors
 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Core.Isos.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
Notation "( c , d )" := (make_catbinprod c d).
Notation "( f #, g )" := (catbinprodmor f g).


Section aux.

Lemma bifunctor_on_morphisms_comm {A B C : category} (F : A ⊠ B ⟶ C) {a a' : A} {b b' : B} (f : a --> a') (g : b --> b') : #F (f #, identity _) · #F (identity _ #, g) = #F (identity _ #, g) · #F (f #, identity _).
Proof.
  rewrite <- !functor_comp.
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite !id_left, !id_right.
  reflexivity.
Qed.

Lemma bifunctor_comp_left {A B C : category} (F : A ⊠ B ⟶ C) {a a' a'' : A} {b : B} (f : a --> a') (g : a' --> a'') : #F (f · g #, identity b) = #F (f #, identity _) · #F (g #, identity _).
Proof.
  rewrite <- (functor_comp F).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  reflexivity.
Qed.

Lemma bifunctor_comp_right {A B C : category} (F : A ⊠ B ⟶ C) {a : A} {b b' b'' : B} (f : b --> b') (g : b' --> b'') : #F (identity a #, f · g) = #F (identity _ #, f) · #F (identity _ #, g).
Proof.
  rewrite <- (functor_comp F).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  reflexivity.
Qed.

End aux.

Section A.

(** For the whole file, fix a monoidal category. *)
Context {Mon_V : monoidal_cat}.

Let I        := I_{Mon_V}.

(** ** Definition *)

(** This definition is based on that on the nLab *)
Section Def.

  Definition enriched_precat_data : UU :=
    ∑ C : UU,                                     (* Type of objects *)
    ∑ mor : C -> C -> ob Mon_V,                     (* Object of morphisms *)
    dirprod
      (∏ x : C, I --> mor x x)                      (* Identities *)
      (∏ x y z : C, mor y z ⊗ mor x y --> mor x z). (* Composition morphism *)

  (** Accessors *)
  Definition enriched_cat_ob    (d : enriched_precat_data) : UU := pr1 d.
  Definition enriched_cat_mor   {d : enriched_precat_data} :
    enriched_cat_ob d -> enriched_cat_ob d -> ob Mon_V := pr1 (pr2 d).
  Definition enriched_cat_identity    {d : enriched_precat_data} :
    ∏ x : enriched_cat_ob d, I --> enriched_cat_mor x x := pr1 (pr2 (pr2 d)).
  Definition enriched_cat_comp {d : enriched_precat_data} (x y z : enriched_cat_ob d) :
    enriched_cat_mor y z ⊗ enriched_cat_mor x y --> enriched_cat_mor x z :=
    pr2 (pr2 (pr2 d)) x y z.

  Coercion enriched_cat_ob : enriched_precat_data >-> UU.

  (** Constructor. Use like so: [use make_enriched_cat_data] *)
  Definition make_enriched_precat_data (C : UU) (mor : ∏ x y : C, ob Mon_V)
             (ids : ∏ x : C, I --> mor x x)
             (assoc : ∏ x y z : C, mor y z ⊗ mor x y --> mor x z) :
    enriched_precat_data.
  Proof.
    unfold enriched_precat_data.
    use tpair; [|use tpair; [|use make_dirprod]].
    - exact C.
    - exact mor.
    - exact ids.
    - exact assoc.
  Defined.

  Section Axioms.
    Context (e : enriched_precat_data).

    (** Associativity axiom for enriched categories:
<<
          (C(c, d) ⊗ C(b, c)) ⊗ C(a, b) --------> C(c, d) ⊗ (C(b, c) ⊗ C(a, b))
                        |                                        |
                ∘ ⊗ identity  |                                identity ⊗ ∘  |
                        V                                        V
                C(b, d) ⊗ C(a, b) -----> C(a, d) <------ C(c, d) ⊗ C(a, c)
>>
    *)

    Definition enriched_assoc_ax : UU :=
      ∏ a b c d : enriched_cat_ob e,
      (enriched_cat_comp b c d #⊗ (identity _))
        · enriched_cat_comp a _ _ =
      mon_lassociator _ _ _
        · ((identity _ #⊗ enriched_cat_comp _ _ _)
          · enriched_cat_comp _ _ _).

    Lemma isaprop_enriched_assoc_ax :
      has_homsets Mon_V -> isaprop (enriched_assoc_ax).
    Proof.
      intro hsV; do 4 (apply impred; intro); apply hsV.
    Defined.

    (** Identity axiom(s) for enriched categories:
<<
          I ⊗ C(a, b) ---> C(b, b) ⊗ C(a, b)
                      \         |
                       \        V
                           C(a, b)
>>
        (And the symmetrized version.)
    *)
    Definition enriched_id_ax : UU :=
      ∏ a b : enriched_cat_ob e,
        dirprod
          (enriched_cat_identity b #⊗ (identity _) · enriched_cat_comp a b b = mon_lunitor _)
          ((identity _ #⊗ enriched_cat_identity a) · enriched_cat_comp a a b = mon_runitor _).


  End Axioms.

  Definition enriched_precat : UU :=
    ∑ d : enriched_precat_data, (enriched_id_ax d) × (enriched_assoc_ax d).

  Definition enriched_precat_to_enriched_precat_data :
    enriched_precat -> enriched_precat_data := pr1.
  Coercion enriched_precat_to_enriched_precat_data :
    enriched_precat >-> enriched_precat_data.

  Definition make_enriched_precat (d : enriched_precat_data) (idax : enriched_id_ax d)
             (assocax : enriched_assoc_ax d) : enriched_precat :=
    tpair _ d (make_dirprod idax assocax).

  (** Accessors *)
  Definition enriched_id_left {A : enriched_precat} (a b : A) : enriched_cat_identity b #⊗ (identity _) · enriched_cat_comp a b b = mon_lunitor _ := pr1 (pr1 (pr2 A) _ _).

  Definition enriched_id_right {A : enriched_precat} (a b : A) : (identity _ #⊗ enriched_cat_identity a) · enriched_cat_comp a a b = mon_runitor _ := pr2 (pr1 (pr2 A) _ _).

  Definition enriched_assoc {A : enriched_precat} (a b c d : A) : (enriched_cat_comp b c d #⊗ (identity _)) · enriched_cat_comp a _ _ = mon_lassociator _ _ _ · ((identity _ #⊗ enriched_cat_comp _ _ _) · enriched_cat_comp _ _ _) := pr2 (pr2 A) a b c d.

End Def.

(** *** Enriched functors *)

Section Functors.
  Context {D E : enriched_precat}.

  Definition enriched_functor_data : UU :=
    ∑ F : enriched_cat_ob D -> enriched_cat_ob E,
      ∏ x y : enriched_cat_ob D,
        Mon_V⟦enriched_cat_mor x y, enriched_cat_mor (F x) (F y)⟧.

  Definition make_enriched_functor_data
    (F : enriched_cat_ob D -> enriched_cat_ob E)
    (mor : ∏ x y : enriched_cat_ob D,
       Mon_V⟦enriched_cat_mor x y, enriched_cat_mor (F x) (F y)⟧)
    : enriched_functor_data :=
    tpair _ F mor.

  (** Accessors *)
  Definition enriched_functor_on_objects (F : enriched_functor_data) :
    enriched_cat_ob D -> enriched_cat_ob E := pr1 F.
  Coercion enriched_functor_on_objects : enriched_functor_data >-> Funclass.
  Definition enriched_functor_on_morphisms (F : enriched_functor_data) :
    ∏ x y : enriched_cat_ob D,
      Mon_V⟦enriched_cat_mor x y, enriched_cat_mor (F x) (F y)⟧ := pr2 F.

  Section Axioms.
    Context (F : enriched_functor_data).

    Definition enriched_functor_unit_ax : UU :=
      ∏ a : enriched_cat_ob D,
      enriched_cat_identity a · enriched_functor_on_morphisms F a a
      =
      enriched_cat_identity (F a).

    Definition enriched_functor_comp_ax : UU :=
      ∏ a b c : enriched_cat_ob D,
      enriched_cat_comp a b c · enriched_functor_on_morphisms F a c
      =
      (enriched_functor_on_morphisms F b c) #⊗  (enriched_functor_on_morphisms F a b)
      · enriched_cat_comp _ _ _.
  End Axioms.

  Definition enriched_functor : UU :=
    ∑ d : enriched_functor_data,
      enriched_functor_unit_ax d × enriched_functor_comp_ax d.

  (** Constructor *)

  Definition make_enriched_functor (d : enriched_functor_data)
    (uax : enriched_functor_unit_ax d) (cax : enriched_functor_comp_ax d) :
    enriched_functor :=
    tpair _ d (make_dirprod uax cax).

  (** Coercion to *_data *)

  Definition enriched_functor_to_enriched_functor_data (F : enriched_functor) :
    enriched_functor_data := pr1 F.
  Coercion enriched_functor_to_enriched_functor_data :
    enriched_functor >-> enriched_functor_data.

  (** Accessors for axioms*)

  Definition enriched_functor_on_identity (F : enriched_functor) :
    enriched_functor_unit_ax F := (pr1 (pr2 F)).

  Definition enriched_functor_on_comp (F : enriched_functor) :
    enriched_functor_comp_ax F := (pr2 (pr2 F)).
End Functors.

Arguments enriched_functor_data _ _ : clear implicits.
Arguments enriched_functor _ _ : clear implicits.

Definition enriched_functor_identity (A : enriched_precat) : enriched_functor A A.
Proof.
  use make_enriched_functor.
  - use make_enriched_functor_data.
    + intro a.
      exact a.
    + intros x y.
      exact (identity _).
  - intro a.
    apply id_right.
  - abstract
      (intros a b c;
       simpl ;
       rewrite tensor_id_id ;
       rewrite id_left, id_right;
       reflexivity).
Defined.

(** *** Composition of enriched functors *)

Definition enriched_functor_comp_data
           {P Q R : enriched_precat}
           (F : enriched_functor_data P Q) (G : enriched_functor_data Q R) :
  enriched_functor_data P R.
Proof.
  use make_enriched_functor_data.
  - exact (λ x, G (F x)).
  - intros x y; cbn.
    refine (_ · (enriched_functor_on_morphisms G (F x) (F y))).
    apply (enriched_functor_on_morphisms F).
Defined.

Definition enriched_functor_comp
           {P Q R : enriched_precat}
           (F : enriched_functor P Q) (G : enriched_functor Q R) :
  enriched_functor P R.
Proof.
  use make_enriched_functor.
  - apply (enriched_functor_comp_data F G).
  - (** Unit axioms *)
    intros a.
    unfold enriched_functor_comp_data; cbn.
    refine (assoc _ _ _ @ _).
    refine (maponpaths (fun f => f · _) (pr1 (pr2 F) a) @ _).
    apply enriched_functor_on_identity.
  - (** Composition axioms *)
    intros a b c; cbn.
    refine (assoc _ _ _ @ _).
    refine (maponpaths (fun f => f · _) (enriched_functor_on_comp F _ _ _) @ _).
    rewrite tensor_comp_mor.
    (* Get rid of the common prefix *)
    refine (_ @ assoc _ _ _).
    refine (!assoc _ _ _ @ _).
    apply (maponpaths (fun f => _ · f)).

    apply enriched_functor_on_comp.
Defined.

(*
  TODO
  Definition enriched_functor_data_eq {A B : enriched_precat Mon_V} {F G : enriched_functor_data _ A B} : (∏ a : A, F a = G a) -> (∏ (a a' : A), enriched_functor_on_morphisms F a a' = enriched_functor_on_morphisms G a a') -> F = G.
*)

Definition enriched_functor_eq {A B : enriched_precat} {F G : enriched_functor A B} : (enriched_functor_to_enriched_functor_data F = enriched_functor_to_enriched_functor_data G) -> F = G.
Proof.
  intro H.
  use total2_paths_b.
  - assumption.
  - apply proofirrelevance.
    apply isapropdirprod.
    + apply impred_isaprop.
      intro.
      apply homset_property.
    + repeat (apply impred_isaprop;intro).
      apply homset_property.
Defined.

Section UnderlyingMorphisms.

Definition underlying_morphism {A : enriched_precat} (x y : A) := I --> enriched_cat_mor x y.

Definition precompose_underlying_morphism {A : enriched_precat} {x y : A} (z : A) (f : underlying_morphism x y) : enriched_cat_mor y z --> enriched_cat_mor x z := (mon_rinvunitor _ · (identity _ #⊗ f) · enriched_cat_comp _ _ _).

Definition postcompose_underlying_morphism {A : enriched_precat} (x : A) {y z : A} (f : underlying_morphism y z) : enriched_cat_mor x y --> enriched_cat_mor x z := (mon_linvunitor _ · (f #⊗ identity _) · enriched_cat_comp _ _ _).

Definition precompose_identity {A : enriched_precat} {x y : A} : precompose_underlying_morphism y (enriched_cat_identity x) = identity _.
Proof.
  unfold precompose_underlying_morphism.
  rewrite assoc'.
  apply (transportb (λ f, _ · f = _) (enriched_id_right _ _)).
  apply mon_rinvunitor_runitor.
Qed.

Definition postcompose_identity {A : enriched_precat} {x y : A} : postcompose_underlying_morphism x (enriched_cat_identity y) = identity _.
Proof.
  unfold postcompose_underlying_morphism.
  rewrite assoc'.
  apply (transportb (λ h, _ · h = _) (enriched_id_left _ _)).
  apply mon_linvunitor_lunitor.
Qed.

Lemma precompose_underlying_morphism_enriched_cat_comp {A : enriched_precat} {w x y z : A} (f : underlying_morphism w x) : ((identity _ #⊗ precompose_underlying_morphism y f) · enriched_cat_comp w y z = enriched_cat_comp x y z · precompose_underlying_morphism z f)%cat.
Proof.
  unfold precompose_underlying_morphism.
  rewrite !assoc.
  rewrite tensor_rinvunitor.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    apply idpath.
  }
  refine (!_).
  rewrite assoc.
  rewrite (assoc' _ _ (enriched_cat_comp w x z)).
  rewrite (@enriched_assoc A).
  rewrite !assoc.
  rewrite !tensor_comp_id_l.
  do 2 apply cancel_postcomposition.
  rewrite assoc'.
  rewrite <- tensor_id_id.
  apply pathsinv0.
  etrans.
  {
    apply cancel_precomposition.
    apply tensor_lassociator.
  }
  rewrite assoc.
  apply cancel_postcomposition.
  rewrite <- mon_rinvunitor_triangle.
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  apply mon_rassociator_lassociator.
Qed.

Lemma enriched_cat_comp_underlying_morphism_middle {A : enriched_precat} {w x y z : A} (f : underlying_morphism x y) : ((identity _ #⊗ postcompose_underlying_morphism w f) · enriched_cat_comp w y z = (precompose_underlying_morphism z f #⊗ identity _) · enriched_cat_comp w x z).
Proof.
  unfold precompose_underlying_morphism, postcompose_underlying_morphism.
  rewrite !tensor_comp_id_r, !tensor_comp_id_l.
  apply pathsinv0.
  rewrite assoc'.
  rewrite (@enriched_assoc A).
  rewrite !assoc.
  do 2 apply cancel_postcomposition.
  rewrite assoc'.
  etrans.
  {
    apply cancel_precomposition.
    apply tensor_lassociator.
  }
  rewrite assoc.
  apply cancel_postcomposition.
  rewrite mon_inv_triangle.
  apply idpath.
Qed.

Lemma postcompose_underlying_morphism_enriched_cat_comp {A : enriched_precat} {w x y z : A} (f : underlying_morphism y z) : ((postcompose_underlying_morphism x f #⊗ identity _) · enriched_cat_comp w x z = enriched_cat_comp w x y · postcompose_underlying_morphism w f).
Proof.
  unfold postcompose_underlying_morphism.
  rewrite !assoc.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    apply idpath.
  }
  refine (!_).
  rewrite assoc.
  rewrite !tensor_comp_id_r.
  rewrite assoc'.
  rewrite (@enriched_assoc A).
  rewrite !assoc.
  do 2 apply cancel_postcomposition.
  rewrite assoc'.
  etrans.
  {
    apply cancel_precomposition.
    apply tensor_lassociator.
  }
  rewrite assoc.
  rewrite tensor_id_id.
  apply cancel_postcomposition.
  apply mon_linvunitor_triangle.
Qed.

Definition postcompose_underlying_morphism_composite {A : enriched_precat} (w : A) {x y z : A} (f : underlying_morphism x y) (g : underlying_morphism y z) : postcompose_underlying_morphism w (f · postcompose_underlying_morphism _ g) = postcompose_underlying_morphism _ f · postcompose_underlying_morphism _ g.
Proof.
  unfold postcompose_underlying_morphism.
  rewrite !tensor_comp_id_r.
  rewrite !assoc'.
  do 2 apply cancel_precomposition.
  rewrite enriched_assoc.
  rewrite !assoc.
  apply cancel_postcomposition.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_lassociator.
    apply idpath.
  }
  simpl.
  rewrite assoc.
  rewrite tensor_id_id.
  rewrite assoc.
  rewrite mon_linvunitor_triangle.
  rewrite !assoc'.
  rewrite <- tensor_split'.
  rewrite tensor_split.
  rewrite !assoc.
  apply cancel_postcomposition.
  apply pathsinv0.
  apply tensor_linvunitor.
Qed.

Definition precompose_underlying_morphism_composite {A : enriched_precat} (w : A) {x y z : A} (f : underlying_morphism x y) (g : underlying_morphism y z) : precompose_underlying_morphism w (f · postcompose_underlying_morphism _ g) = precompose_underlying_morphism _ g · precompose_underlying_morphism _ f.
Proof.
  unfold postcompose_underlying_morphism, precompose_underlying_morphism.
  rewrite !tensor_comp_id_l.
  rewrite !assoc.
  rewrite (assoc' _ (enriched_cat_comp y z w)).
  rewrite tensor_rinvunitor.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    do 3 apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    apply idpath.
  }
  refine (!_).
  rewrite assoc.
  rewrite (assoc' _ _ (enriched_cat_comp x y w)).
  rewrite enriched_assoc.
  rewrite !assoc.
  do 2 apply cancel_postcomposition.
  rewrite <- tensor_id_id.
  rewrite !assoc'.
  apply cancel_precomposition.
  do 2 rewrite assoc.
  rewrite tensor_lassociator.
  rewrite assoc.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- mon_rinvunitor_triangle.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      apply mon_rassociator_lassociator.
    }
    apply id_left.
  }
  rewrite <- !tensor_comp_mor.
  apply maponpaths.
  rewrite !assoc.
  rewrite tensor_linvunitor.
  rewrite tensor_rinvunitor.
  rewrite mon_rinvunitor_I_mon_linvunitor_I.
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- tensor_split, <- tensor_split'.
  apply idpath.
Qed.

Definition underlying_morphism_compose_swap {A : enriched_precat} {x y z : A} (f : underlying_morphism x y) (g : underlying_morphism y z) : f · postcompose_underlying_morphism _ g = g · precompose_underlying_morphism _ f.
Proof.
  unfold postcompose_underlying_morphism.
  rewrite !assoc.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_left, id_right.
    apply idpath.
  }
  unfold precompose_underlying_morphism.
  rewrite !assoc.
  refine (maponpaths (λ z, z · _) _).
  rewrite tensor_rinvunitor.
  rewrite !assoc'.
  rewrite <- tensor_split'.
  refine (maponpaths (λ z, z · _) _).
  apply mon_linvunitor_I_mon_rinvunitor_I.
Qed.

Definition pre_post_compose_commute {A : enriched_precat} {w x y z : A} (f : underlying_morphism w x) (g : underlying_morphism y z) : precompose_underlying_morphism _ f · postcompose_underlying_morphism _ g = postcompose_underlying_morphism _ g · precompose_underlying_morphism _ f.
Proof.
  unfold postcompose_underlying_morphism.
  rewrite !assoc.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split.
    rewrite tensor_split'.
    apply idpath.
  }
  rewrite !assoc'.
  do 2 apply cancel_precomposition.
  unfold precompose_underlying_morphism.
  rewrite !assoc.
  rewrite tensor_comp_id_l.
  rewrite tensor_rinvunitor.
  refine (!_).
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    apply idpath.
  }
  rewrite !assoc'.
  rewrite (enriched_assoc w).
  rewrite !assoc.
  do 2 apply cancel_postcomposition.
  rewrite assoc'.
  rewrite <- tensor_id_id.
  rewrite tensor_lassociator.
  rewrite !assoc.
  rewrite <- mon_rinvunitor_triangle.
  etrans.
  {
    refine (maponpaths (λ z, z · _) _).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply mon_rassociator_lassociator.
    }
    apply id_right.
  }
  rewrite tensor_comp_id_l.
  apply idpath.
Qed.

Definition enriched_functor_on_postcompose {A B : enriched_precat} (F : enriched_functor A B) {y z : A} (f : underlying_morphism y z) (x : A) : postcompose_underlying_morphism x f · enriched_functor_on_morphisms F _ _ = enriched_functor_on_morphisms F _ _ · postcompose_underlying_morphism _ (f · enriched_functor_on_morphisms F _ _).
Proof.
  unfold postcompose_underlying_morphism.
  rewrite !assoc.
  rewrite tensor_linvunitor.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_left, id_right.
    apply idpath.
  }
  apply cancel_precomposition.
  rewrite enriched_functor_on_comp.
  rewrite !assoc.
  apply cancel_postcomposition.
  rewrite <- tensor_comp_mor.
  rewrite id_left.
  apply idpath.
Qed.

Definition enriched_functor_on_precompose {A B : enriched_precat} (F : enriched_functor A B) {x y : A} (f : underlying_morphism x y) (z : A) : precompose_underlying_morphism z f · enriched_functor_on_morphisms F _ _ = enriched_functor_on_morphisms F _ _ · precompose_underlying_morphism _ (f · enriched_functor_on_morphisms F _ _).
Proof.
  unfold precompose_underlying_morphism.
  rewrite !assoc.
  rewrite tensor_rinvunitor.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_left, id_right.
    apply idpath.
  }
  apply cancel_precomposition.
  rewrite enriched_functor_on_comp.
  rewrite !assoc.
  apply cancel_postcomposition.
  rewrite <- tensor_comp_mor.
  rewrite id_left.
  apply idpath.
Qed.

End UnderlyingMorphisms.

Section NatTrans.

Definition enriched_nat_trans_data {A B : enriched_precat} (F G : enriched_functor A B) := ∏ a : A, underlying_morphism (F a) (G a).

Definition enriched_nat_trans_law {A B : enriched_precat} {F G : enriched_functor A B} (a : enriched_nat_trans_data F G) := ∏ (x y : A), enriched_functor_on_morphisms F x y · postcompose_underlying_morphism _ (a y) = enriched_functor_on_morphisms G x y · precompose_underlying_morphism _ (a x).

Definition enriched_nat_trans {A B : enriched_precat} (F G : enriched_functor A B) := ∑ a : enriched_nat_trans_data F G, enriched_nat_trans_law a.

Definition enriched_nat_trans_data_from_enriched_nat_trans {A B : enriched_precat} {F G : enriched_functor A B} (a : enriched_nat_trans F G) : ∏ a : A, I --> enriched_cat_mor (F a) (G a) := pr1 a.
Coercion enriched_nat_trans_data_from_enriched_nat_trans : enriched_nat_trans >-> Funclass.

Definition enriched_nat_trans_ax {A B : enriched_precat} {F G : enriched_functor A B} (a : enriched_nat_trans F G) :enriched_nat_trans_law a := pr2 a.

Definition make_enriched_nat_trans {A B : enriched_precat} {F G : enriched_functor A B} a l : enriched_nat_trans F G := (a,, l).

Definition enriched_nat_trans_eq {A B : enriched_precat} {F G : enriched_functor A B} {a a' : enriched_nat_trans F G} : (∏ x : A, a x = a' x) -> a = a'.
Proof.
  intro H.
  use total2_paths_b.
  - apply funextsec.
    assumption.
  - apply proofirrelevance.
    repeat (apply impred_isaprop; intro).
    apply homset_property.
Defined.

Definition enriched_nat_trans_identity {A B : enriched_precat} (F : enriched_functor A B) : enriched_nat_trans F F.
Proof.
  use make_enriched_nat_trans.
  - intro x.
    apply enriched_cat_identity.
  - abstract (intros x y;
    rewrite precompose_identity, postcompose_identity;
    reflexivity).
Defined.

Definition enriched_nat_trans_comp {A B : enriched_precat} {F G H : enriched_functor A B} (a : enriched_nat_trans F G) (b : enriched_nat_trans G H) : enriched_nat_trans F H.
Proof.
  use make_enriched_nat_trans.
  - intro x.
    exact (a x · postcompose_underlying_morphism _ (b x)).
  - abstract (intros x y;
    rewrite postcompose_underlying_morphism_composite;
    rewrite assoc;
    rewrite enriched_nat_trans_ax;
    rewrite assoc';
    rewrite pre_post_compose_commute;
    rewrite assoc;
    rewrite enriched_nat_trans_ax;
    rewrite precompose_underlying_morphism_composite;
    apply assoc').
Defined.

End NatTrans.

Section EnrichedFunctorCategory.

Lemma isaset_enriched_nat_trans {A B : enriched_precat} (F G : enriched_functor A B) : isaset (enriched_nat_trans F G).
Proof.
  apply isaset_total2.
  - apply impred_isaset.
    intro.
    apply homset_property.
  - intro.
    apply isasetaprop.
    repeat (apply impred_isaprop; intro).
    apply homset_property.
Qed.

Lemma enriched_nat_trans_assoc {A B : enriched_precat} {F G H K : enriched_functor A B} (f : enriched_nat_trans F G) (g : enriched_nat_trans G H) (h : enriched_nat_trans H K) : enriched_nat_trans_comp f (enriched_nat_trans_comp g h) = enriched_nat_trans_comp (enriched_nat_trans_comp f g) h.
Proof.
  apply enriched_nat_trans_eq.
  intro x.
  cbn.
  rewrite postcompose_underlying_morphism_composite.
  apply assoc.
Qed.

Definition enriched_functor_precategory_data (A B : enriched_precat) : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact (enriched_functor A B).
    + intros F G.
      exact (enriched_nat_trans F G).
  - intros c.
    apply enriched_nat_trans_identity.
  - intros a b c f g.
    exact (enriched_nat_trans_comp f g).
Defined.

Definition enriched_functor_category (A B : enriched_precat) : category.
Proof.
  use make_category.
  - use make_precategory.
    + exact (enriched_functor_precategory_data A B).
    + repeat split;simpl.
      * abstract (intros;
        apply enriched_nat_trans_eq;
        intro;
        cbn;
        rewrite underlying_morphism_compose_swap;
        rewrite precompose_identity;
        apply id_right).
      * abstract (intros;
        apply enriched_nat_trans_eq;
        intro;
        cbn;
        rewrite postcompose_identity;
        apply id_right).
      * abstract (intros;
        apply enriched_nat_trans_assoc).
      * abstract (intros;
        apply pathsinv0;
        apply enriched_nat_trans_assoc).
  - intros a b.
    apply isaset_enriched_nat_trans.
Defined.

End EnrichedFunctorCategory.

Section Whisker.

Definition pre_whisker {A B C : enriched_precat} (F : enriched_functor A B) {G H : enriched_functor B C} (a : enriched_nat_trans G H) : enriched_nat_trans (enriched_functor_comp F G) (enriched_functor_comp F H).
Proof.
  use make_enriched_nat_trans.
  - intro x.
    exact (a (F x)).
  - abstract (intros x y;
    simpl;
    rewrite !assoc';
    apply cancel_precomposition;
    apply enriched_nat_trans_ax).
Defined.

Definition post_whisker {A B C : enriched_precat} {F G : enriched_functor A B} (a : enriched_nat_trans F G) (H : enriched_functor B C) : enriched_nat_trans (enriched_functor_comp F H) (enriched_functor_comp G H).
Proof.
  use make_enriched_nat_trans.
  - intro x.
    exact (a x · enriched_functor_on_morphisms H _ _).
  - abstract (intros x y;
    simpl;
    rewrite !assoc';
    rewrite <- enriched_functor_on_precompose, <- enriched_functor_on_postcompose;
    rewrite !assoc;
    apply cancel_postcomposition;
    apply enriched_nat_trans_ax).
Defined.

End Whisker.

Section Unit.

Definition unit_enriched_precat_data : enriched_precat_data.
Proof.
  use make_enriched_precat_data.
  - exact unit.
  - intros.
    exact (I_{Mon_V}).
  - intros.
    exact (identity _).
  - intros.
    exact (mon_lunitor _).
Defined.

Definition unit_enriched_precat : enriched_precat.
Proof.
  use make_enriched_precat.
  - exact unit_enriched_precat_data.
  - split; cbn.
    + abstract
        (rewrite tensor_id_id ;
         apply id_left).
    + abstract
        (rewrite tensor_id_id ;
         rewrite id_left ;
         apply mon_lunitor_I_mon_runitor_I).
  - abstract
      (intros a b c d ;
       cbn ;
       rewrite !assoc ;
       apply cancel_postcomposition ;
       rewrite mon_lunitor_I_mon_runitor_I ;
       rewrite mon_triangle ;
       rewrite mon_runitor_I_mon_lunitor_I ;
       apply idpath).
Defined.

Definition element_functor_data {A : enriched_precat} (a : A) : enriched_functor_data unit_enriched_precat A.
Proof.
  use make_enriched_functor_data.
  - intro.
    exact a.
  - intros x y.
    induction x, y.
    apply enriched_cat_identity.
Defined.

Definition element_functor_unit_ax {A : enriched_precat} (a : A) : enriched_functor_unit_ax (element_functor_data a).
Proof.
  intro t.
  induction t.
  simpl.
  apply id_left.
Qed.

Definition element_functor_comp_ax {A : enriched_precat} (a : A) : enriched_functor_comp_ax (element_functor_data a).
Proof.
  intros t t' t''.
  induction t, t', t''.
  cbn.
  rewrite tensor_split.
  rewrite !assoc'.
  rewrite enriched_id_left.
  rewrite tensor_lunitor.
  apply idpath.
Qed.

Definition element_functor {A : enriched_precat} (a : A) : enriched_functor unit_enriched_precat A.
Proof.
  use make_enriched_functor.
  - exact (element_functor_data a).
  - exact (element_functor_unit_ax a).
  - exact (element_functor_comp_ax a).
Defined.

End Unit.

End A.

Arguments enriched_precat_data _ : clear implicits.
Arguments enriched_precat _ : clear implicits.
Arguments enriched_functor_data {_} _ _.
Arguments enriched_functor {_} _ _.
Arguments unit_enriched_precat _ : clear implicits.
