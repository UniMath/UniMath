(** * Coslice categories

Author: Langston Barrett (@siddharthist), March 2018
*)

(** ** Contents:

- Definition of coslice categories, x/C

*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
(* Require Import UniMath.Foundations.Propositions. *)
(* Require Import UniMath.Foundations.Sets. *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

(** for second construction: *)
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

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
    where f · h = g

*)
Section coslice_cat_def.

Context (C : category) (x : C).

(** Accessor functions *)
Definition coslicecat_ob := ∑ a, C⟦x,a⟧.
Definition coslicecat_mor (f g : coslicecat_ob) := ∑ h, pr2 f · h = pr2 g.
Definition coslicecat_ob_object (f : coslicecat_ob) : ob C := pr1 f.
Definition coslicecat_ob_morphism (f : coslicecat_ob) : C⟦x, coslicecat_ob_object f⟧ := pr2 f.
Definition coslicecat_mor_morphism {f g : coslicecat_ob} (h : coslicecat_mor f g) :
  C⟦coslicecat_ob_object f, coslicecat_ob_object g⟧ := pr1 h.
Definition coslicecat_mor_comm {f g : coslicecat_ob} (h : coslicecat_mor f g) :
  (coslicecat_ob_morphism f) · (coslicecat_mor_morphism h) =
  (coslicecat_ob_morphism g) := pr2 h.

(** Definitions *)
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

Lemma is_precategory_coslice_precat_data :
  is_precategory coslice_precat_data.
Proof.
  use make_is_precategory; intros; unfold comp_coslice_precat;
    cbn; apply subtypePairEquality.
  * intro; apply C.
  * apply id_left.
  * intro; apply C.
  * apply id_right.
  * intro; apply C.
  * apply assoc.
  * intro; apply C.
  * apply assoc'.
Defined.

Definition coslice_precat : precategory :=
  (_,,is_precategory_coslice_precat_data).

Lemma has_homsets_coslice_precat : has_homsets (coslice_precat).
Proof.
  intros a b.
  induction a as [a f]; induction b as [b g]; simpl.
  apply (isofhleveltotal2 2); [ apply C | intro h].
  apply isasetaprop; apply C.
Qed.

Definition coslice_cat : category := make_category _ has_homsets_coslice_precat.

End coslice_cat_def.

Section coslice_cat_displayed.

Context (C : category) (x : C).

Definition coslice_cat_disp : disp_cat C.
Proof.
  use tpair.
  - use tpair.
    + use make_disp_cat_ob_mor.
      * intro a. exact (x --> a).
      * intros a b f g h. exact (f · h = g).
    + split.
      * intros a f.
        apply id_right.
      * intros a1 a2 a3 h h' f1 f2 f3 Hyph Hyph'.
        cbn.
        rewrite assoc.
        rewrite Hyph.
        exact Hyph'.
  - repeat split; intros; try apply C.
    apply isasetaprop; apply C.
Defined.

Definition coslice_cat_total : category := total_category coslice_cat_disp.

End coslice_cat_displayed.
