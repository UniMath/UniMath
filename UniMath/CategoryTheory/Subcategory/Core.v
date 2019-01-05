(** ** Sub(pre)categories

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)
Reorganized and expanded: Langston Barrett (@siddharthist) (March 2018)

*)


(** ** Contents :

- Subprecategories
  - A sub-precategory forms a precategory ([carrier_of_sub_precategory])
  - (Inclusion) functor from a sub-precategory to the ambient precategory
    ([sub_precategory_inclusion])
- Subcategories ([subcategory])
- Restriction of a functor to a subcategory
*)


Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Local Open Scope cat.

(** ** Definitions *)

(** A sub-precategory is specified through a predicate on objects
    and a dependent predicate on morphisms
    which is compatible with identity and composition
*)

Definition is_sub_precategory {C : precategory}
    (C' : hsubtype C)
    (Cmor' : ∏ a b : C, hsubtype (a --> b)) :=
  (∏ a : C, C' a ->  Cmor' _ _ (identity a)) ×
  (∏ (a b c : C) (f: a --> b) (g : b --> c),
            Cmor' _ _ f -> Cmor' _ _  g -> Cmor' _ _  (f · g)).

Definition sub_precategories (C : precategory) :=
  total2 (fun C' : (hsubtype (ob C)) × (∏ a b:ob C, hsubtype (a --> b)) =>
           is_sub_precategory (pr1 C') (pr2 C')).

(** We have a coercion [carrier] turning every predicate [P] on a type [A] into the
     total space [ { a : A & P a} ].

   For later, we define some projections with the appropriate type, also to
   avoid confusion with the aforementioned coercion.
*)

Definition sub_precategory_predicate_objects {C : precategory}
     (C': sub_precategories C):
       hsubtype (ob C) := pr1 (pr1 C').

Definition sub_ob {C : precategory}(C': sub_precategories C): UU :=
     (*carrier*) (sub_precategory_predicate_objects C').


Definition sub_precategory_predicate_morphisms {C : precategory}
        (C':sub_precategories C) (a b : C) : hsubtype (a --> b) := pr2 (pr1 C') a b.

Definition sub_precategory_morphisms {C : precategory}(C':sub_precategories C)
      (a b : C) : UU :=  sub_precategory_predicate_morphisms C' a b.

(** Projections for compatibility of the predicate with identity and
    composition.
*)

Definition sub_precategory_id (C : precategory) (C':sub_precategories C) :
   ∏ a : ob C,
       sub_precategory_predicate_objects C' a ->
       sub_precategory_predicate_morphisms  C' _ _ (identity a) :=
         dirprod_pr1 (pr2 C').

Definition sub_precategory_comp (C : precategory) (C':sub_precategories C) :
   ∏ (a b c: ob C) (f: a --> b) (g : b --> c),
          sub_precategory_predicate_morphisms C' _ _ f ->
          sub_precategory_predicate_morphisms C' _ _ g ->
          sub_precategory_predicate_morphisms C' _ _  (f · g) :=
        dirprod_pr2 (pr2 C').

(** An object of a subprecategory is an object of the original precategory. *)

Definition precategory_object_from_sub_precategory_object (C:precategory)
         (C':sub_precategories C) (a : sub_ob C') :
    ob C := pr1 a.
Coercion precategory_object_from_sub_precategory_object :
     sub_ob >-> ob.

(** A morphism of a subprecategory is also a morphism of the original precategory. *)

Definition precategory_morphism_from_sub_precategory_morphism (C:precategory)
          (C':sub_precategories C) (a b : ob C)
           (f : sub_precategory_morphisms C' a b) : a --> b := pr1 f .
Coercion precategory_morphism_from_sub_precategory_morphism :
         sub_precategory_morphisms >-> precategory_morphisms.

(** *** A sub-precategory forms a precategory. *)

Definition sub_precategory_ob_mor (C : precategory)(C':sub_precategories C) :
     precategory_ob_mor.
Proof.
  exists (sub_ob C').
  exact (λ a b, @sub_precategory_morphisms _ C' a b).
Defined.

(*
Coercion sub_precategory_ob_mor : sub_precategories >-> precategory_ob_mor.
*)


Definition sub_precategory_data (C : precategory)(C':sub_precategories C) :
      precategory_data.
Proof.
  exists (sub_precategory_ob_mor C C').
  split.
    intro c.
    exists (identity (C:=C) (pr1 c)).
    apply sub_precategory_id.
    apply (pr2 c).
  intros a b c f g.
  exists (compose (pr1 f) (pr1 g)).
  apply sub_precategory_comp.
  apply (pr2 f). apply (pr2 g).
Defined.

(** A useful lemma for equality in the sub-precategory. *)

Lemma eq_in_sub_precategory (C : precategory)(C':sub_precategories C)
      (a b : sub_ob C') (f g : sub_precategory_morphisms C' a b) :
          pr1 f = pr1 g -> f = g.
Proof.
  intro H.
  apply (total2_paths_f H).
  apply proofirrelevance.
  apply pr2.
Qed.

(*
Lemma eq_in_sub_precategory2 (C : precategory)(C':sub_precategories C)
     (a b : sub_ob C') (f g : a --> b)
 (pf : sub_precategory_predicate_morphisms C' _ _ f)
 (pg : sub_precategory_predicate_morphisms C' _ _ g):
  f = g -> (tpair (λ f, sub_precategory_predicate_morphisms _ _ _ f) f pf) =
      (tpair (λ f, sub_precategory_predicate_morphisms _ _ _ f) g pg).
Proof.
  intro H.
  apply (two_arg_paths_f H).
  destruct H.
  apply (two_arg_paths_f (idpath _ )).
*)

Definition is_precategory_sub_precategory (C : precategory)(C':sub_precategories C) :
    is_precategory (sub_precategory_data C C').
Proof.
  repeat split;
  simpl; intros.
  unfold sub_precategory_comp;
  apply eq_in_sub_precategory; simpl;
  apply id_left.
  apply eq_in_sub_precategory. simpl.
  apply id_right.
  apply eq_in_sub_precategory.
  cbn.
  apply assoc.
  apply eq_in_sub_precategory.
  cbn.
  apply assoc'.
Defined.

Definition carrier_of_sub_precategory (C : precategory)(C':sub_precategories C) :
   precategory := tpair _ _ (is_precategory_sub_precategory C C').

Coercion carrier_of_sub_precategory : sub_precategories >-> precategory.

(** An object satisfying the predicate is an object of the subprecategory *)
Definition precategory_object_in_subcat {C : precategory} {C':sub_precategories C}
   (a : ob C) (p : sub_precategory_predicate_objects C' a) :
       ob C' := tpair _ a p.

(** A morphism satisfying the predicate is a morphism of the subprecategory *)
Definition precategory_morphisms_in_subcat {C : precategory} {C':sub_precategories C}
   {a b : ob C'}(f : pr1 a --> pr1 b)
   (p : sub_precategory_predicate_morphisms C' (pr1 a) (pr1 b) (f)) :
       precategory_morphisms (C:=C') a b := tpair _ f p.

(** *** (Inclusion) functor from a sub-precategory to the ambient precategory *)

Definition sub_precategory_inclusion_data (C : precategory) (C':sub_precategories C):
  functor_data C' C.
Proof.
  exists (@pr1 _ _ ).
  intros a b.
  exact (@pr1 _ _ ).
Defined.

Definition is_functor_sub_precategory_inclusion (C : precategory)
         (C':sub_precategories C) :
    is_functor  (sub_precategory_inclusion_data C C').
Proof.
  split; simpl.
  unfold functor_idax . intros.  apply (idpath _ ).
  unfold functor_compax . intros.  apply (idpath _ ).
Qed.

Definition sub_precategory_inclusion (C : precategory) (C' : sub_precategories C) :
    functor C' C := tpair _ _ (is_functor_sub_precategory_inclusion C C').

(** ** Subcategories *)

(** The hom-types of a subprecategory are sets if the hom-types of the original
    category are. *)

Lemma is_set_sub_precategory_morphisms {C : precategory} (hs: has_homsets C)
                                       (C' : sub_precategories C) (a b : ob C) :
  isaset (sub_precategory_morphisms C' a b).
Proof.
  apply isofhlevel_hsubtype, hs.
Defined.

Definition sub_precategory_morphisms_set {C : precategory} (hs: has_homsets C)
  (C':sub_precategories C) (a b : ob C) : hSet :=
    tpair _ (sub_precategory_morphisms C' a b)
        (is_set_sub_precategory_morphisms hs C' a b).

Definition subcategory (C : category) (C' : sub_precategories C) : category.
Proof.
  use category_pair.
  - exact (carrier_of_sub_precategory C C').
  - intros ? ?.
    apply is_set_sub_precategory_morphisms.
    apply homset_property.
Defined.

(** ** Restriction of a functor to a subcategory *)

Definition restrict_functor_to_sub_precategory {C D : precategory}
           (C' : sub_precategories C) (F : functor C D) : functor C' D.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + exact (F ∘ precategory_object_from_sub_precategory_object _ C')%functions.
    + intros ? ?.
      apply (# F ∘ precategory_morphism_from_sub_precategory_morphism _ C' _ _)%functions.
  - use dirprodpair.
    + intro; apply (functor_id F).
    + intros ? ? ? ? ?; apply (functor_comp F).
Defined.