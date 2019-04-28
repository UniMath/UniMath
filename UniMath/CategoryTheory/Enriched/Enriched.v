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
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Section A.

(** For the whole file, fix a monoidal category. *)
Context (Mon_V : monoidal_precat).
Let V        := monoidal_precat_precat Mon_V.
Let I        := monoidal_precat_unit Mon_V.
Let tensor   := monoidal_precat_tensor Mon_V.
Let α        := monoidal_precat_associator Mon_V.
Let l_unitor := monoidal_precat_left_unitor Mon_V.
Let r_unitor := monoidal_precat_right_unitor Mon_V.

Notation "X ⊗ Y"  := (tensor (X , Y)) : enriched.
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31) : enriched.
Local Open Scope enriched.

(** ** Definition *)

(** This definition is based on that on the nLab *)
Section Def.

  Definition enriched_precat_data : UU :=
    ∑ C : UU,                                     (* Type of objects *)
    ∑ mor : C -> C -> ob V,                         (* Object of morphisms *)
    dirprod
      (∏ x : C, I --> mor x x)                      (* Identities *)
      (∏ x y z : C, mor y z ⊗ mor x y --> mor x z). (* Composition morphism *)

  (** Accessors *)
  Definition enriched_cat_ob    (d : enriched_precat_data) : UU := pr1 d.
  Definition enriched_cat_mor   {d : enriched_precat_data} :
    enriched_cat_ob d -> enriched_cat_ob d -> ob V := pr1 (pr2 d).
  Definition enriched_cat_id    {d : enriched_precat_data} :
    ∏ x : enriched_cat_ob d, I --> enriched_cat_mor x x := pr1 (pr2 (pr2 d)).
  Definition enriched_cat_comp {d : enriched_precat_data} (x y z : enriched_cat_ob d) :
    enriched_cat_mor y z ⊗ enriched_cat_mor x y --> enriched_cat_mor x z :=
    pr2 (pr2 (pr2 d)) x y z.

  (** Constructor. Use like so: [use make_enriched_cat_data] *)
  Definition make_enriched_precat_data (C : UU) (mor : ∏ x y : C, ob V)
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
                ∘ ⊗ id  |                                id ⊗ ∘  |
                        V                                        V
                C(b, d) ⊗ C(a, b) -----> C(a, d) <------ C(c, d) ⊗ C(a, c)
        >>
    *)

    Definition enriched_assoc_ax : UU :=
      ∏ a b c d : enriched_cat_ob e,
      (enriched_cat_comp b c d #⊗ (identity _))
        · enriched_cat_comp a _ _ =
      pr1 α ((_, _) , _)
        · ((identity _ #⊗ enriched_cat_comp _ _ _)
          · enriched_cat_comp _ _ _).

    Lemma isaprop_enriched_assoc_ax :
      has_homsets V -> isaprop (enriched_assoc_ax).
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
          (enriched_cat_id b #⊗ (identity _) · enriched_cat_comp a b b = pr1 l_unitor _)
          ((identity _ #⊗ enriched_cat_id a) · enriched_cat_comp a a b = pr1 r_unitor _).


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

End Def.

(** *** Enriched functors *)

Section Functors.
  Context (D E : enriched_precat).

  Definition enriched_functor_data : UU :=
    ∑ F : enriched_cat_ob D -> enriched_cat_ob E,
      ∏ x y : enriched_cat_ob D,
        V⟦enriched_cat_mor x y, enriched_cat_mor (F x) (F y)⟧.

  Definition make_enriched_functor_data
    (F : enriched_cat_ob D -> enriched_cat_ob E)
    (mor : ∏ x y : enriched_cat_ob D,
       V⟦enriched_cat_mor x y, enriched_cat_mor (F x) (F y)⟧)
    : enriched_functor_data :=
    tpair _ F mor.

  (** Accessors *)
  Definition enriched_functor_on_objects (F : enriched_functor_data) :
    enriched_cat_ob D -> enriched_cat_ob E := pr1 F.
  Coercion enriched_functor_on_objects : enriched_functor_data >-> Funclass.
  Definition enriched_functor_on_morphisms (F : enriched_functor_data) :
    ∏ x y : enriched_cat_ob D,
      V⟦enriched_cat_mor x y, enriched_cat_mor (F x) (F y)⟧ := pr2 F.

  Notation "# F"  := (enriched_functor_on_morphisms F) : enriched.

  Section Axioms.
    Context (F : enriched_functor_data).

    Definition enriched_functor_unit_ax : UU :=
      ∏ a : enriched_cat_ob D,
        enriched_cat_id a · #F a a = enriched_cat_id (F a).

    Definition enriched_functor_comp_ax : UU :=
      ∏ a b c : enriched_cat_ob D,
        enriched_cat_comp a b c · #F a c =
        (#F b c) #⊗  (#F a b) · enriched_cat_comp _ _ _.
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

Notation "# F"  := (enriched_functor_on_morphisms _ _ F) : enriched.

(** *** Composition of enriched functors *)

Definition enriched_functor_comp_data
           {P Q R : enriched_precat}
           (F : enriched_functor_data P Q) (G : enriched_functor_data Q R) :
  enriched_functor_data P R.
Proof.
  use make_enriched_functor_data.
  - exact (λ x, G (F x)).
  - intros x y; cbn.
    refine (_ · (# G (F x) (F y))).
    apply (# F).
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
    refine (maponpaths (fun f => f · _) (enriched_functor_on_comp _ _ F _ _ _) @ _).
    refine (_ @ !maponpaths (fun f => f · _) (tensor_comp _ _ _ _ _)).

    (* Get rid of the common prefix *)
    refine (_ @ assoc _ _ _).
    refine (!assoc _ _ _ @ _).
    apply (maponpaths (fun f => _ · f)).

    apply enriched_functor_on_comp.
Defined.

End A.
