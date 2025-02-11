(** * Display Map Category
    Contents:
    - add display map as a subclass of morphisms [display_map C]
    - add an interpretation as a subcategory of [codomain C]
    - show that this subcategory is a cleaving [disp_map_cleaving]
    - define the inclusion functor [ι : disp_map_cat D ⇒ disp_codomain C]
    - TODO: show the inclusion functor preserves cartesian arrows
    - define the map between display maps [map_dispmap D D']
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
(* Require Import UniMath.CategoryTheory.DisplayedCats.Isos. *)
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
(* Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations. *)
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
(* Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor. *)
(* Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC. *)
Local Open Scope cat.

(** ** Display Map *)
Definition displaymap_data (C : category) :=
  ∏ a b : C, a --> b -> hProp.

Definition has_map_pullbacks {C : category} (D : displaymap_data C) :=
  ∏ (a b c : C) (f : b --> a) (d : c --> a),
    D _ _ d -> ∑ (p : Pullback f d), D _ _ (PullbackPr1 p).

Definition display_map (C : category) :=
  ∑ (D : displaymap_data C), has_map_pullbacks D.

(** **** Display Map Category *)
(** This is based on the definition for [disp_codomain]. *)
(** See: Codomain.v *)

Definition disp_map_ob_mor {C : category} (D : display_map C) : disp_cat_ob_mor C.
Proof.
  exists (λ x : C, ∑ y (f : y --> x), (pr1 D) _ _ f).
  intros x y dx dy f.
  exact (∑ df : pr1 dx --> pr1 dy, df · pr12 dy = pr12 dx · f).
Defined.

Definition disp_map_id_comp
  {C : category} {D : display_map C}
  : disp_cat_id_comp _ (disp_map_ob_mor D).
Proof.
  split; cbn.
  - intros x xx. exists (identity (pr1 xx)).
    rewrite id_left, id_right. reflexivity.
  - intros x y z f g xx yy zz ff gg. exists (pr1 ff · pr1 gg).
    rewrite <- assoc. rewrite (pr2 gg). rewrite assoc, (pr2 ff).
    symmetry. exact (assoc _ _ _).
Defined.

Definition disp_map_data {C : category} (D : display_map C) : disp_cat_data _ := (disp_map_ob_mor D ,, disp_map_id_comp).

Proposition transportf_disp_map
  {C : category} {D : display_map C}
  {x y : C} {dx : disp_map_data D x} {dy : disp_map_data D y}
  {f g : x --> y}
  (p : f = g) (ff : dx -->[f] dy)
  : pr1 (transportf (mor_disp dx dy) p ff) = pr1 ff.
Proof.
  refine (pr1_transportf (A := C⟦_, _⟧) _ _ @ _).
  rewrite transportf_const.
  reflexivity.
Qed.

Proposition transportb_disp_map
  {C : category} {D : display_map C}
  {x y : C} {dx : disp_map_data D x} {dy : disp_map_data D y}
  {f g : x --> y}
  (p : g = f) (ff : dx -->[f] dy)
  : pr1 (transportb (mor_disp dx dy) p ff) = pr1 ff.
Proof.
  exact (transportf_disp_map _ _).
Qed.

Definition eq_disp_map_mor
  {C : category} {D : display_map C}
  {x y : C} {dx : disp_map_data D x} {dy : disp_map_data D y}
  {f : x --> y} {ff gg : dx -->[f] dy}
  (p :  pr1 ff = pr1 gg)
  : ff = gg.
Proof.
  use subtypePath.
  - exact (λ _, homset_property _ _ _ _ _).
  - exact p.
Qed.

Definition disp_map_axioms {C : category} {D : display_map C} : disp_cat_axioms C (disp_map_data D).
Proof.
  use tpair; try (use tpair); try (use tpair); intros; cbn in *.
  - use eq_disp_map_mor; cbn.
    rewrite transportb_disp_map with (ff := ff).
    exact (id_left _).
  - use eq_disp_map_mor; cbn.
    rewrite transportb_disp_map with (ff := ff).
    exact (id_right _).
  - use eq_disp_map_mor.
    rewrite transportb_disp_map with (ff := (pr1 ff · pr1 gg · pr1 hh ,, _)).
    exact (assoc _ _ _).
  - intros. apply isaset_total2.
    + exact (homset_property _ _ _).
    + intros. apply isasetaprop. exact (homset_property _ _ _ _ _).
Qed.

Definition disp_map_cat {C : category} (D : display_map C) : disp_cat C
  := (disp_map_data D ,, disp_map_axioms).

Definition disp_map_pullback
  {C : category} {D : display_map C}
  {Γ Γ' : C} (f : Γ' --> Γ)
  (d : disp_map_cat D Γ)
  := pr2 D _ _ _ f (pr12 d) (pr22 d).

(** Proof that [disp_map_cat] is a [cleaving]. *)
Definition disp_map_cartesian_candidate
  {C : category} {D : display_map C}
  {Γ Γ' : C} (f : Γ' --> Γ)
  (d : disp_map_cat D Γ)
  : ∑ (d' : disp_map_cat D Γ'), d' -->[f] d.
Proof.
  use tpair.
  - use tpair.
    + exact (PullbackObject (pr1 (disp_map_pullback f d))).
    + exact (PullbackPr1 (pr1 (disp_map_pullback f d)) ,, pr2 (disp_map_pullback f d)).
  - use tpair.
    + exact (PullbackPr2 (pr1 (disp_map_pullback f d))).
    + exact (!(PullbackSqrCommutes (pr1 (disp_map_pullback f d)))).
Defined.

Definition disp_map_is_cartesian
  {C : category} {D : display_map C}
  {Γ Γ' : C} (f : Γ' --> Γ)
  (d : disp_map_cat D Γ)
  : is_cartesian (pr2 (disp_map_cartesian_candidate f d)).
Proof.
  intros Γ'' g d'' [t Ht].
  use tpair.
  - use tpair.
    + use ((PullbackArrow (pr1 (disp_map_pullback f d)) (pr1 d'') (pr12 d'' · g) t ((!(assoc _ _ _)) @ !Ht)) ,, PullbackArrow_PullbackPr1 _ _ _ _ _).
    + simpl. use subtypePath.
      { exact (λ _, homset_property _ _ _ _ _). }
      { simpl. exact (PullbackArrow_PullbackPr2 _ _ _ _ _). }
  - simpl. intros [[p Hp] Hcomp]. use subtypePath.
    + intros [p' Hp'].
      exact (homsets_disp (g · f) d'' _ _ (t,,Ht)).
    + simpl. use subtypePath.
      { exact (λ _, homset_property _ _ _ _ _). }
      {
        simpl. apply PullbackArrowUnique'.
        - exact Hp.
        - apply base_paths in Hcomp. simpl in Hcomp. exact Hcomp.
      }
Defined.


Definition disp_map_cleaving
  {C : category} {D : display_map C}
  : cleaving (disp_map_cat D).
Proof.
  intros Γ Γ' f d.
  exists (pr1 (disp_map_cartesian_candidate f d)).
  exists (pr2 (disp_map_cartesian_candidate f d)).
  exact (disp_map_is_cartesian f d).
Defined.

Definition disp_map_inclusion
  {C : category} (D : display_map C)
  : disp_functor (functor_identity C) (disp_map_cat D) (disp_codomain C).
Proof.
  use tpair; use tpair; simpl.
  - exact (λ _ d, pr1 d ,, pr12 d).
  - exact (λ _ _ _ _ _ ff, ff).
  - simpl. intros x dx. use eq_disp_map_mor.
    reflexivity.
  - simpl. intros x y z dx dy dz f g ff gg. use eq_disp_map_mor.
    reflexivity.
Defined.
Notation "'ι'" := disp_map_inclusion.


(** **** Map of DispMaps *)
Definition preserves_maps {C C' : category} (D : display_map C) (D' : display_map C') (F : C ⟶ C') :=
  ∏ (a b : C) (d : a --> b), (pr1 D) _ _ d -> (pr1 D') _ _ (#F d).

Definition preserves_pullbacks {C C' : category} (D : display_map C) (D' : display_map C') (F : C ⟶ C') :=
  ∏ (a b c : C) (f : b --> a) (g : c --> a), (pr1 D) _ _ g -> Pullback f g -> Pullback (#F f) (#F g).

Definition map_dispmap {C C' : category} (D : display_map C) (D' : display_map C') :=
  ∑ (F: C ⟶ C'), preserves_maps D D' F × preserves_pullbacks D D' F.

Definition functor_from_map {C C' : category} (D : display_map C) (D' : display_map C') (F : map_dispmap D D') : C ⟶ C' := pr1 F.
Coercion functor_from_map : map_dispmap >-> functor.
