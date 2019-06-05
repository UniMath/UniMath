(* =================================================================================== *)
(** * Modules over relative monads                                                     *)
(* =================================================================================== *)

(* ----------------------------------------------------------------------------------- *)
(** Contents:                                                                          *)
(**                                                                                    *)
(**   - Definition of module over a relative monads [RelModule]                        *)
(**   - Functoriality for modules [mlift]                                              *)
(**   - Morphisms between relative modules (over the same monad).                      *)
(**                                                                                    *)
(** Written by: Marco Maggesi (started March 2018)                                     *)
(* ----------------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monads.RelativeMonads.

Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Miscellanea                                                                     *)
(* ----------------------------------------------------------------------------------- *)

Definition isaprop_RelMonad_axioms {C D : precategory_data} {J : C ⟶ D}
           (hs : has_homsets D) (R : RelMonad_data J)
  : isaprop (RelMonad_axioms R).
Proof.
  repeat apply isapropdirprod; repeat (apply impred; intros); apply hs.
Qed.

(* ----------------------------------------------------------------------------------- *)
(** ** Definition of module over a relative monad.                                     *)
(* ----------------------------------------------------------------------------------- *)

Section RelModule_Definition.

  Context {C D : precategory_data} {J : C ⟶ D}.

  Definition RelModule_data (R : RelMonad_data J) : UU
    := ∑ F : C → D, ∏ c d, D ⟦J c, R d⟧ → D ⟦F c, F d⟧.

  Definition make_relmodule_data (R : RelMonad_data J) (F : C → D)
             (mbind : ∏ c d, D ⟦J c, R d⟧ → D ⟦F c, F d⟧)
    : RelModule_data R
    := F,, mbind.

  Definition RelModule_ob {R : RelMonad_data J} (M : RelModule_data R)
    : C → D
    := pr1 M.
  Coercion RelModule_ob : RelModule_data >-> Funclass.

  Section Projections_and_Laws.

    Context {R : RelMonad_data J}.

    Definition mbind (M : RelModule_data R)
               {c d} (f : D⟦J c, R d⟧)
      : D ⟦M c, M d⟧
      := pr2 M _ _ f.

    Definition mlift (M : RelModule_data R) {a b} (f : C ⟦a, b⟧)
      : D ⟦pr1 M a, pr1 M b⟧
      := mbind M (#J f · r_eta R _).

    Definition relmodule_functor_data (M : RelModule_data R)
      : functor_data C D
      := make_functor_data M (λ a b (f : a -->b), mlift M f).

    Definition RelModule_laws (M : RelModule_data R) : UU
      := RelMonad_axioms R
       × (∏ c, mbind M (r_eta R c) = identity _ )
       × (∏ c d e (f : D ⟦J c, R d⟧) (g : D ⟦J d, R e⟧),
          mbind M f · mbind M g = mbind M (f · r_bind R g)).

    Coercion relmonad_axiom_from_relmodule {M : RelModule_data R} (X : RelModule_laws M)
      : RelMonad_axioms R
      := pr1 X.

    Definition mbind_r_eta {M : RelModule_data R} (X : RelModule_laws M)
      : ∏ c, mbind M (r_eta R c) = identity _ := pr1 (pr2 X).

    Definition mbind_mbind {M : RelModule_data R} (X : RelModule_laws M)
      : ∏ c d e (f : D ⟦J c, R d⟧) (g : D ⟦J d, R e⟧),
        mbind M f · mbind M g = mbind M (f · r_bind R g)
      := pr2 (pr2 X).

    Lemma isaprop_RelModule_laws (hs : has_homsets D) (M : RelModule_data R)
      : isaprop (RelModule_laws M).
    Proof.
      apply isapropdirprod.
      - apply isaprop_RelMonad_axioms, hs.
      - apply isapropdirprod; repeat (apply impred; intros); apply hs.
    Qed.


    Lemma mbind_mlift {M : RelModule_data R} (X : RelModule_laws M) {c d e : C} (f : J c --> R d) (g : d --> e)
      : mbind M f · mlift M g = mbind M (f · r_lift R g).
    Proof.
      apply (mbind_mbind X).
    Qed.


  End Projections_and_Laws.
End RelModule_Definition.


(* We make a separate section with stronger hypothesis [RelMonad] to state
   another fusion law involving [r_lift]. *)
Section Projections_and_Laws_2.

Context {C : precategory_data} {D : precategory}{J : C ⟶ D} {R : RelMonad J} {M : RelModule_data R} (X : RelModule_laws M).

Lemma mlift_mbind {c d e : C} (f : c --> d) (g : J d --> R e)
  : mlift M f · mbind M g = mbind M (#J f · g).
Proof.
  unfold mlift.
  etrans. { apply (mbind_mbind X). }
          apply maponpaths.
  etrans. { apply pathsinv0, assoc. }
          apply maponpaths.
  apply (r_eta_r_bind R).
Qed.

End Projections_and_Laws_2.


(* ----------------------------------------------------------------------------------- *)
(** ** Packing the full structure of Relative Module together.                         *)
(* ----------------------------------------------------------------------------------- *)

Definition RelModule {C D : precategory_data} {J : C ⟶ D} (R : RelMonad_data J) : UU
  := ∑ M : RelModule_data R, RelModule_laws M.

Definition make_RelModule {C D : precategory_data} {J : C ⟶ D} (R : RelMonad_data J)
           (M : RelModule_data R) (HM : RelModule_laws M)
  : RelModule R
  := (M,, HM).

Coercion RelModule_data_from_RelModule {C D : precategory_data} {J : C ⟶ D}
         {R : RelMonad_data J} (M : RelModule R)
  : RelModule_data R
  := pr1 M.

Coercion RelModule_laws_from_RelModule {C D : precategory_data} {J : C ⟶ D}
         {R : RelMonad_data J} (M : RelModule R)
  : RelModule_laws M
  := pr2 M.

(* ----------------------------------------------------------------------------------- *)
(** ** Functoriality of Modules                                                        *)
(* ----------------------------------------------------------------------------------- *)

Section Functor_from_RelModule.

  Context {C : precategory_data} {D : precategory} {J : C ⟶ D}.

  Lemma mlift_id {R : RelMonad_data J} {M : RelModule_data R} (X : RelModule_laws M) (c : C) :
    mlift M (identity c) = identity (M c).
  Proof.
    transitivity (mbind M (r_eta R c)).
    2: apply (mbind_r_eta X).
    unfold mlift. cbn. apply maponpaths.
    etrans.
    2: apply id_left.
    apply maponpaths_2.
    apply functor_id.
  Qed.

  Context {R : RelMonad J} {M : RelModule_data R} (X : RelModule_laws M).

  Lemma mlift_mlift {c d e : C} (f : c --> d) (g : d --> e) :
    mlift M f · mlift M g = mlift M (f · g).
  Proof.
    unfold mlift at 2.
    etrans. { apply (mlift_mbind X). }
    unfold mlift. apply maponpaths.
    etrans. { apply assoc. }
    apply maponpaths_2.
    apply pathsinv0, functor_comp.
  Qed.

  Definition functor_data_from_relmodule : functor_data C D
    := functor_data_constr C D
                           (RelModule_ob M : C → D)
                           (λ a b (f : a --> b), mlift M f).

  Definition is_functor_mlift : is_functor functor_data_from_relmodule.
  Proof.
    split.
    - red; intro a. apply (mlift_id X).
    - red. intros. cbn. apply pathsinv0. apply mlift_mlift.
  Defined.

  Definition functor_from_relmodule : C ⟶ D
    := make_functor functor_data_from_relmodule is_functor_mlift.

End Functor_from_RelModule.

(* ----------------------------------------------------------------------------------- *)
(** ** Morphisms of modules over a fixe relative monad.                                *)
(* ----------------------------------------------------------------------------------- *)

Section RelModule_Morphism_Definition.
Section Part1.
  Context {C D : precategory_data} {J : C ⟶ D} {R : RelMonad_data J}.

  Definition is_relmodule_mor (M N : RelModule_data R) (φ : ∏ a : C, M a --> N a) : UU
    := (∏ a b (f : J a --> R b), mbind M f · φ b = φ a · mbind N f).

  Lemma isaprop_RelModule_Mor_laws (hs : has_homsets D) (M N : RelModule_data R)
        (φ : ∏ a : C, M a --> N a)
    : isaprop (is_relmodule_mor M N φ).
  Proof.
    repeat (apply impred; intro); apply hs.
  Qed.

  Definition RelModule_Mor (M N : RelModule R) : UU :=
    ∑ (φ : ∏ a : C, M a --> N a), is_relmodule_mor M N φ.

  Definition relmodule_mor_map {M N : RelModule R} (φ : RelModule_Mor M N)
    : ∏ a : C, M a --> N a
    := pr1 φ.
  Coercion relmodule_mor_map : RelModule_Mor >-> Funclass.

  Coercion relmodule_mor_property {M N : RelModule R} (φ : RelModule_Mor M N)
    : is_relmodule_mor M N φ
    := pr2 φ.

End Part1.
(** now with [D : precategory, R : RelMonad J] *)
Section Part2.
  Context {C : precategory_data} {D : precategory} {J : C ⟶ D} {R : RelMonad J}.

  Definition is_nat_trans_relmodule_mor {M N : RelModule R} {φ : ∏ a : C, M a --> N a}
             (Hφ : is_relmodule_mor M N φ)
    : is_nat_trans (functor_from_relmodule M) (functor_from_relmodule N) φ.
  Proof.
    intros a b f. cbn. unfold mlift. apply Hφ.
  Defined.

  Definition RelModule_Mor_equiv (hs : has_homsets D)
  {M N : RelModule R} (φ ψ : RelModule_Mor M N)
  : φ = ψ ≃ (pr1 φ = pr1 ψ).
  Proof.
    apply subtypeInjectivity; intro a.
    apply isaprop_RelModule_Mor_laws, hs.
  Defined.

  Definition nat_trans_from_relmodule_mor {M N : RelModule R} (φ : RelModule_Mor M N)
    : functor_from_relmodule M ⟹ functor_from_relmodule N
    := make_nat_trans (functor_from_relmodule M) (functor_from_relmodule N)
                    φ
                    (is_nat_trans_relmodule_mor φ).

  Definition is_relmodule_mor_id (M : RelModule R)
    : is_relmodule_mor M M (λ a, identity (M a)).
  Proof.
    intros a b f. etrans.
    - apply id_right.
    - apply pathsinv0, id_left.
  Qed.

  Definition relmodule_mor_id (M : RelModule R) : RelModule_Mor M M :=
    ((λ a, identity (M a)),, is_relmodule_mor_id M).

  Definition is_relmodule_mor_comp {L M N : RelModule R}
             {φ} (φ_mor : is_relmodule_mor L M φ)
             {ψ} (ψ_mor : is_relmodule_mor M N ψ)
    : is_relmodule_mor L N (λ a, φ a · ψ a).
  Proof.
    intros a b f.
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2, φ_mor. }
    etrans. { apply pathsinv0, assoc. }
    etrans. 2: apply assoc.
    apply maponpaths.
    apply ψ_mor.
  Qed.

  Definition relmodule_mor_comp {L M N : RelModule R}
             (φ : RelModule_Mor L M) (ψ : RelModule_Mor M N)
    : RelModule_Mor L N
    := ((λ a, φ a · ψ a),, is_relmodule_mor_comp φ ψ).

End Part2.

End RelModule_Morphism_Definition.

(* ----------------------------------------------------------------------------------- *)
(** ** Category of modules over a fixed relative monad.                                *)
(* ----------------------------------------------------------------------------------- *)

Section RelModule_Category.

  Context {C : precategory_data} {D : precategory} {J : C ⟶ D} (R : RelMonad J).

  Definition relmodule_precategory_ob_mor : precategory_ob_mor
    := make_precategory_ob_mor (RelModule R) RelModule_Mor.

  Definition relmodule_precategory_data : precategory_data
    := make_precategory_data
         relmodule_precategory_ob_mor
         relmodule_mor_id
         (λ M N P (φ : RelModule_Mor M N) (ψ : RelModule_Mor N P),
          relmodule_mor_comp φ ψ).

  Lemma is_precategory_relmodule (hs : has_homsets D)
    : is_precategory relmodule_precategory_data.
  Proof.
    apply is_precategory_one_assoc_to_two.
    repeat split.
    - intros x y f.
      apply (invmap (RelModule_Mor_equiv hs _ _ )).
      apply funextsec; intros a. apply id_left.
    - intros x y f.
      apply (invmap (RelModule_Mor_equiv hs _ _ )).
      apply funextsec; intros a. apply id_right.
    - intros x y z w f g h.
      apply (invmap (RelModule_Mor_equiv hs _ _ )).
      apply funextsec. intros a. apply assoc.
  Qed.

  Definition RelModule_Precategory (hs : has_homsets D)
    : precategory
    := make_precategory relmodule_precategory_data (is_precategory_relmodule hs).

  Definition has_homsets_RelModule_Precategory (hs : has_homsets D)
    : has_homsets (RelModule_Precategory hs).
  Proof.
    red. cbn. intros M N.
    apply isaset_total2.
    - apply impred_isaset. intros. apply hs.
    - intros P. apply isasetaprop.
      apply isaprop_RelModule_Mor_laws. apply hs.
  Defined.

End RelModule_Category.

(* ----------------------------------------------------------------------------------- *)
(** ** Tautological module                                                             *)
(*                                                                                     *)
(** Any relative monad is a left module over itself.                                   *)
(* ----------------------------------------------------------------------------------- *)

Section Tautological_RelModule.

  Context {C D : precategory_data} {J : C ⟶ D} (R : RelMonad J).

  Definition tautological_RelModule_data : RelModule_data R
    := make_relmodule_data R R (λ a b (f : D⟦J a, R b⟧), r_bind R f).

  Lemma tautological_RelModule_law  : RelModule_laws tautological_RelModule_data.
  Proof.
    split.
    - exact R.
    - repeat split; cbn; intros.
      + apply (r_bind_r_eta R).
      + apply (r_bind_r_bind R).
  Qed.

  Definition tautological_RelModule : RelModule R
    := make_RelModule R tautological_RelModule_data tautological_RelModule_law.

End Tautological_RelModule.