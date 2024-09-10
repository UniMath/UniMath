Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** Just like how context morphisms in a CwA can be built up out of terms, similarly, the basic building-block for functors into (total cats of) displayed categories will be analogous to a term.

We call it a _section_ (though we define it intrinsically, not as a section in a (bi)category), since it corresponds to a section of the forgetful functor. *)

Section Sections.

  Definition section_disp_data {C} (D : disp_cat C) : UU
    := ∑ (Fob : forall x:C, D x),
      (forall (x y:C) (f:x --> y), Fob x -->[f] Fob y).

  Definition section_disp_on_objects {C} {D : disp_cat C}
             (F : section_disp_data D) (x : C)
    := pr1 F x : D x.

  Coercion section_disp_on_objects : section_disp_data >-> Funclass.

  Definition section_disp_on_morphisms {C} {D : disp_cat C}
             (F : section_disp_data D) {x y : C} (f : x --> y)
    := pr2 F _ _ f : F x -->[f] F y.

  Notation "# F" := (section_disp_on_morphisms F)
                      (at level 3) : mor_disp_scope.

  Definition section_disp_axioms {C} {D : disp_cat C}
             (F : section_disp_data D) : UU
    := ((forall x:C, # F (identity x) = id_disp (F x))
          × (forall (x y z : C) (f : x --> y) (g : y --> z),
                # F (f · g) = (# F f) ;; (# F g))).

  Definition section_disp {C} (D : disp_cat C) : UU
    := total2 (@section_disp_axioms C D).

  Lemma isaprop_section_disp_axioms {C : category} {D : disp_cat C} (F : section_disp_data D)
    (Hmor : ∏ (x y : C) (f : x --> y) (c : D x) (d : D y), isaset (c -->[f] d)) :
    isaprop (section_disp_axioms F).
  Proof.
    apply isapropdirprod.
    - apply impred; intro.
      apply Hmor.
    - do 5 (apply impred; intro).
      apply Hmor.
  Qed.

  Definition section_disp_data_from_section_disp {C} {D : disp_cat C}
             (F : section_disp D) := pr1 F.

  Coercion section_disp_data_from_section_disp
    : section_disp >-> section_disp_data.

  Definition section_disp_id {C} {D : disp_cat C} (F : section_disp D)
    := pr1 (pr2 F).

  Definition section_disp_comp {C} {D : disp_cat C} (F : section_disp D)
    := pr2 (pr2 F).

End Sections.

(* Natural transformations of sections  *)
Section Section_transformation.

Definition section_nat_trans_disp_data
    {C : category}
    {D : disp_cat C}
    (F F' : section_disp D) : UU :=
  ∏ (x : C), F x -->[identity _] F' x.

Definition section_nat_trans_disp_axioms
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp_data F F') : UU :=
  ∏ x x' (f : x --> x'),
      transportf _
      (id_right _ @ !(id_left _))
      (section_disp_on_morphisms F f ;; nt x') =
    nt x ;; section_disp_on_morphisms F' f.

Lemma isaprop_section_nat_trans_disp_axioms
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp_data F F') :
  isaprop (section_nat_trans_disp_axioms nt).
Proof.
  do 3 (apply impred; intro).
  apply homsets_disp.
Qed.

Definition section_nat_trans_disp
    {C : category}
    {D : disp_cat C}
    (F F': section_disp D) : UU :=
  ∑ (nt : section_nat_trans_disp_data F F'), section_nat_trans_disp_axioms nt.

Lemma isaset_section_nat_trans_disp
    {C : category}
    {D : disp_cat C}
    (F F': section_disp D) :
  isaset (section_nat_trans_disp F F').
Proof.
  apply (isofhleveltotal2 2).
  - apply impred. intro t. apply homsets_disp.
  - intro x. apply isasetaprop. apply isaprop_section_nat_trans_disp_axioms.
Qed.

Definition section_nt_disp_data_from_section_nt_disp
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : section_nat_trans_disp_data F F'
  := pr1 nt.

Definition section_nat_trans_data_from_section_nat_trans_disp_funclass
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
  ∏ x : ob C, F x -->[identity _]  F' x := section_nt_disp_data_from_section_nt_disp nt.
Coercion section_nat_trans_data_from_section_nat_trans_disp_funclass :
    section_nat_trans_disp >-> Funclass.

Definition section_nt_disp_axioms_from_section_nt_disp
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : section_nat_trans_disp_axioms nt
  := pr2 nt.

Definition section_nat_trans_id
    {C : category}
    {D : disp_cat C}
    (F : section_disp D)
    : section_nat_trans_disp F F.
Proof.
  use tpair.
  - intro.
    exact (id_disp _).
  - simpl.
    intros x x' f.

    rewrite id_left_disp, id_right_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
Defined.

Definition section_nat_trans_comp
    {C : category}
    {D : disp_cat C}
    {F F' F'': section_disp D}
    (FF' : section_nat_trans_disp F F')
    (F'F'' : section_nat_trans_disp F' F'') :
  section_nat_trans_disp F F''.
Proof.
  use tpair.
  - intro x.
    exact (transportf _ (id_left _) (FF' x ;; F'F'' x)).
  - simpl.
    intros x x' f.

    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.

    rewrite assoc_disp_var, transport_f_f.
    rewrite <- (section_nt_disp_axioms_from_section_nt_disp F'F'').

    rewrite mor_disp_transportf_prewhisker, transport_f_f.

    do 2 rewrite assoc_disp, transport_f_b.
    rewrite <- (section_nt_disp_axioms_from_section_nt_disp FF').

    rewrite mor_disp_transportf_postwhisker, transport_f_f.

    apply maponpaths_2.
    apply homset_property.
Defined.

Lemma section_nat_trans_eq {C : category} {D : disp_cat C}
  (F F' : section_disp D) (a a' : section_nat_trans_disp F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { now apply funextsec. }
  apply (total2_paths_f H').
  apply proofirrelevance.
  apply isaprop_section_nat_trans_disp_axioms.
Qed.

Definition section_nat_trans_id_left
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (FF' : section_nat_trans_disp F F') :
  section_nat_trans_comp (section_nat_trans_id F) FF' = FF'.
Proof.
  use section_nat_trans_eq.
  intro x.
  simpl.
  rewrite id_left_disp.
  rewrite transport_f_b.
  apply transportf_set.
  apply homset_property.
Qed.

Definition section_nat_trans_id_right
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (FF' : section_nat_trans_disp F F') :
  section_nat_trans_comp FF' (section_nat_trans_id F') = FF'.
Proof.
  use section_nat_trans_eq.
  intro x.
  simpl.
  rewrite id_right_disp.
  rewrite transport_f_b.
  apply transportf_set.
  apply homset_property.
Qed.

Definition section_nat_trans_assoc
    {C : category}
    {D : disp_cat C}
    {F1 F2 F3 F4: section_disp D}
    (F12 : section_nat_trans_disp F1 F2)
    (F23 : section_nat_trans_disp F2 F3)
    (F34 : section_nat_trans_disp F3 F4) :
  section_nat_trans_comp F12 (section_nat_trans_comp F23 F34) = section_nat_trans_comp (section_nat_trans_comp F12 F23) F34.
Proof.
  use section_nat_trans_eq.
  intro x.
  simpl.
  rewrite mor_disp_transportf_postwhisker.
  rewrite mor_disp_transportf_prewhisker.
  do 2 rewrite transport_f_f.
  rewrite assoc_disp.
  rewrite transport_f_b.
  apply maponpaths_2.
  apply homset_property.
Qed.

End Section_transformation.
