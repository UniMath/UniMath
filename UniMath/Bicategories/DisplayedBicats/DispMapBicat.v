(**********************************************************************

 Display map bicategories

 A display map bicategory represents a full sub bicategory of the
 internal Street fibrations that also gives rise to a fibration of
 bicategories.

 1. Basic definitions
 2. Examples
 3. Every display map bicategory gives rise to a displayed bicategory

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.InternalStreetFibration.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CodomainFibs.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.Colimits.Pullback.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

(**
1. Basic definitions
 *)
Definition fam_on_1cells
           (B : bicat)
  : UU
  := ∏ (x y : B), x --> y → UU.

Definition has_all_pb
           {B : bicat}
           (P : fam_on_1cells B)
  : UU.
Proof.
  apply TODO.
  (*
          x
          | f
          V
  z ----> y

  if f is in P
  then this diag has a pullback
   *)
Defined.

Definition closed_under_pb
           {B : bicat}
           (P : fam_on_1cells B)
  : UU.
Proof.
  apply TODO.
  (*
  p ----> x
g |       | f
  V       V
  z ----> y

  for every pullback square
  if f is in P
  then g is in P
   *)
Defined.

Definition isPredicate_on_1cells
           {B : bicat}
           (P : fam_on_1cells B)
  : UU
  := ∏ (x y : B), isPredicate (P x y).

Definition disp_map_bicat
           (B : bicat)
  : UU
  := ∑ (P : fam_on_1cells B),
     has_all_pb P
     ×
     closed_under_pb P
     ×
     isPredicate_on_1cells P.

Coercion family_of_disp_map_bicat
         {B : bicat}
         (P : disp_map_bicat B)
  : fam_on_1cells B
  := pr1 P.

Definition fam_of_disp_map_bicat
           {B : bicat}
           (P : disp_map_bicat B)
           {x y : B}
           (f : x --> y)
  : UU
  := pr1 P _ _ f.

Definition disp_map_bicat_has_all_pb
           {B : bicat}
           (P : disp_map_bicat B)
  : has_all_pb P
  := pr12 P.

Definition disp_map_bicat_closed_under_pb
           {B : bicat}
           (P : disp_map_bicat B)
  : closed_under_pb P
  := pr122 P.

Definition disp_map_bicat_isPredicate
           {B : bicat}
           (P : disp_map_bicat B)
  : isPredicate_on_1cells P
  := pr222 P.

Definition make_disp_map_bicat
           {B : bicat}
           (P : fam_on_1cells B)
           (pbP : has_all_pb P)
           (cP : closed_under_pb P)
           (predP : isPredicate_on_1cells P)
  : disp_map_bicat B
  := (P ,, pbP ,, cP ,, predP).

(**
2. Examples
 *)
Definition top_disp_map_bicat
           (B : bicat)
           (pbB : has_pb B)
  : disp_map_bicat B.
Proof.
  use make_disp_map_bicat.
  - exact (λ _ _ _, unit).
  - apply TODO.
  - apply TODO.
  - intros x y f.
    apply isapropunit.
Defined.

Definition bot_disp_map_bicat
           (B : bicat)
           (pbB : has_pb B)
  : disp_map_bicat B.
Proof.
  use make_disp_map_bicat.
  - exact (λ _ _ _, ∅).
  - apply TODO.
  - apply TODO.
  - intros x y f.
    apply isapropempty.
Defined.

Definition meet_disp_map_bicat
           {B : bicat}
           (P Q : disp_map_bicat B)
  : disp_map_bicat B.
Proof.
  use make_disp_map_bicat.
  - exact (λ _ _ f, fam_of_disp_map_bicat P f × fam_of_disp_map_bicat Q f).
  - apply TODO.
  - apply TODO.
  - intros x y f.
    apply isapropdirprod.
    + apply (disp_map_bicat_isPredicate P).
    + apply (disp_map_bicat_isPredicate Q).
Defined.

(**
3. Every display map bicategory gives rise to a displayed bicategory
 *)
Section DispMapBicatToDispBicat.
  Context {B : bicat}
          (P : disp_map_bicat B).

  Definition pred_on_sfibs
    : total_bicat (cod_sfibs B) → UU
    := λ hx, fam_of_disp_map_bicat P (pr122 hx).

  Definition disp_map_bicat_to_disp_bicat
    : disp_bicat B
    := sigma_bicat
         _
         _
         (disp_fullsubbicat
            (total_bicat (cod_sfibs B))
            pred_on_sfibs).

  Definition disp_map_bicat_inclusion_data
    : disp_psfunctor_data
        disp_map_bicat_to_disp_bicat
        (cod_sfibs B)
        (id_psfunctor B).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _) ; simpl.
    - exact (λ x hx, (pr11 hx ,, pr121 hx ,, pr221 hx)).
    - exact (λ x y f hx hy hf, pr1 hf).
    - exact (λ x y f g α hx hy hf hg hα, pr1 hα).
    - simple refine (λ x hx, _).
      use make_cod_sfibs_disp_invertible_2cell.
      + use make_cell_of_internal_sfib_over.
        * apply id2.
        * abstract
            (unfold cell_of_internal_sfib_over_homot ;
             cbn ;
             rewrite id2_rwhisker, id2_right ;
             rewrite lwhisker_id2, id2_left ;
             apply idpath).
      + cbn.
        is_iso.
    - simple refine (λ x y z f g hx hy hz hf hg, _).
      use make_cod_sfibs_disp_invertible_2cell.
      + use make_cell_of_internal_sfib_over.
        * apply id2.
        * abstract
            (unfold cell_of_internal_sfib_over_homot ;
             cbn ;
             rewrite id2_rwhisker, id2_right ;
             rewrite lwhisker_id2, id2_left ;
             apply idpath).
      + cbn.
        is_iso.
  Defined.

  Definition disp_map_bicat_inclusion_is_disp_psfunctor
    : is_disp_psfunctor
        disp_map_bicat_to_disp_bicat
        (cod_sfibs B)
        (id_psfunctor B)
        disp_map_bicat_inclusion_data.
  Proof.
    repeat split ; intro ; intros ;
      (use subtypePath ; [ intro ; apply cellset_property | ]) ; cbn ;
        rewrite transportb_cell_of_internal_sfib_over ; cbn.
    - apply idpath.
    - apply idpath.
    - rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - rewrite id2_rwhisker, lwhisker_id2, !id2_left, !id2_right.
      apply idpath.
    - rewrite id2_left, id2_right.
      apply idpath.
    - rewrite id2_left, id2_right.
      apply idpath.
  Qed.

  Definition disp_map_bicat_inclusion
    : disp_psfunctor
        disp_map_bicat_to_disp_bicat
        (cod_sfibs B)
        (id_psfunctor B).
  Proof.
    simple refine (_ ,, _).
    - exact disp_map_bicat_inclusion_data.
    - exact disp_map_bicat_inclusion_is_disp_psfunctor.
  Defined.
End DispMapBicatToDispBicat.
