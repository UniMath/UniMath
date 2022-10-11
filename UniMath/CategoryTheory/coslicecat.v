(** * Coslice categories

Author: Langston Barrett (@siddharthist), March 2018
*)

(** ** Contents:

- Definition of slice precategories, x/C

*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
(* Require Import UniMath.Foundations.Propositions. *)
(* Require Import UniMath.Foundations.Sets. *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Local Open Scope cat.

(** * Definition of coslice categories *)

(** Given a category C and x : obj C. The coslice category x/C is given by:

  - obj x/C: pairs (a,f) where f : x --> a
  - morphisms (a,f) --> (b,g): morphism h : a --> b with
<<
       x
       | \
       |  \
     f |   \  g
       v    \
       a --> b
          h
>>
    where h · g = f

*)
Section coslice_precat_def.

Context (C : precategory) (x : C).

(** Accessor functions *)
Definition coslicecat_ob := total2 (λ a, C⟦x,a⟧).
Definition coslicecat_mor (f g : coslicecat_ob) := total2 (λ h, pr2 f · h = pr2 g).
Definition coslicecat_ob_object (f : coslicecat_ob) : ob C := pr1 f.
Definition coslicecat_ob_morphism (f : coslicecat_ob) : C⟦x, coslicecat_ob_object f⟧ := pr2 f.
Definition coslicecat_mor_morphism {f g : coslicecat_ob} (h : coslicecat_mor f g) :
  C⟦coslicecat_ob_object f, coslicecat_ob_object g⟧ := pr1 h.
Definition coslicecat_mor_comm {f g : coslicecat_ob} (h : coslicecat_mor f g) :
  (coslicecat_ob_morphism f) · (coslicecat_mor_morphism h) =
  (coslicecat_ob_morphism g) := pr2 h.

(** Defintions *)
Definition coslice_precat_ob_mor : precategory_ob_mor :=
  (coslicecat_ob,,coslicecat_mor).

Definition id_coslice_precat (c : coslice_precat_ob_mor) : c --> c :=
  tpair _ _ (id_right (pr2 c)).

Definition comp_coslice_precat {a b c : coslice_precat_ob_mor}
           (f : a --> b) (g : b --> c) : a --> c.
Proof.
  use tpair.
  - exact (coslicecat_mor_morphism f · coslicecat_mor_morphism g).
  - abstract (refine (assoc _ _ _ @ _);
              refine (maponpaths (λ f, f · _) (coslicecat_mor_comm f) @ _);
              refine (coslicecat_mor_comm g)).
Defined.

Definition coslice_precat_data : precategory_data :=
  make_precategory_data _ id_coslice_precat (@comp_coslice_precat).

Lemma is_precategory_coslice_precat_data (sets : ∏ y, isaset (x --> y)) :
  is_precategory coslice_precat_data.
Proof.
  use make_is_precategory; intros; unfold comp_coslice_precat;
    cbn; apply subtypePairEquality.
  * intro; apply sets.
  * apply id_left.
  * intro; apply sets.
  * apply id_right.
  * intro; apply sets.
  * apply assoc.
  * intro; apply sets.
  * apply assoc'.
Defined.

Definition coslice_precat (sets : ∏ y, isaset (x --> y)) : precategory :=
  (_,,is_precategory_coslice_precat_data sets).

End coslice_precat_def.
