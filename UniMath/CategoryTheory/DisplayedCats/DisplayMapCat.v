(** * Display Map Category
    Contents:
    - add display map as a subclass of morphisms [display_map_class C]
    - add an interpretation as a subcategory of [codomain C]
    - show that this subcategory is a cleaving [display_map_cleaving]
    - define the inclusion functor [ι : display_map_cat D ⇒ disp_codomain C]
    - TODO: show the inclusion functor preserves cartesian arrows
    - define the map between display maps [map_dispmap D D']
    - TODO: show the conversion from a display_map_class to a comprehension category
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Local Open Scope cat.

(** ** Display Map *)
Definition display_map_class_data (C : category) :=
  ∏ a b : C, a --> b -> hProp.
Definition display_map_class_data_to_fun {C} {a b} (D : display_map_class_data C) : a --> b -> hProp := D a b.
Coercion display_map_class_data_to_fun : display_map_class_data >-> Funclass.

Definition has_map_pullbacks {C : category} (D : display_map_class_data C) :=
  ∏ (a b c : C) (f : b --> a) (d : c --> a),
    D _ _ d -> ∑ (p : Pullback d f), D _ _ (PullbackPr2 p).

Definition display_map_class (C : category) :=
  ∑ (D : display_map_class_data C), has_map_pullbacks D.
Definition display_map_class_to_data {C : category} (D : display_map_class C) : display_map_class_data C := pr1 D.
Coercion display_map_class_to_data : display_map_class >-> display_map_class_data.

(** ** Display Map Category *)
(** This is based on the definition for [disp_codomain]. *)
(** See: Codomain.v *)

Definition disp_map_ob_mor {C : category} (D : display_map_class C) : disp_cat_ob_mor C.
Proof.
  exists (λ x : C, ∑ y (f : y --> x), (pr1 D) _ _ f).
  intros x y dx dy f.
  exact (∑ df : pr1 dx --> pr1 dy, df · pr12 dy = pr12 dx · f).
Defined.

Definition disp_map_id_comp
  {C : category} {D : display_map_class C}
  : disp_cat_id_comp _ (disp_map_ob_mor D).
Proof.
  split; cbn.
  - intros x xx. exists (identity (pr1 xx)).
    rewrite id_left, id_right. reflexivity.
  - intros x y z f g xx yy zz ff gg. exists (pr1 ff · pr1 gg).
    rewrite <- assoc. rewrite (pr2 gg). rewrite assoc, (pr2 ff).
    symmetry. exact (assoc _ _ _).
Defined.

Definition display_map_cat_data {C : category} (D : display_map_class C) : disp_cat_data _ := (disp_map_ob_mor D ,, disp_map_id_comp).

Proposition transportf_display_map
  {C : category} {D : display_map_class C}
  {x y : C} {dx : display_map_cat_data D x} {dy : display_map_cat_data D y}
  {f g : x --> y}
  (p : f = g) (ff : dx -->[f] dy)
  : pr1 (transportf (mor_disp dx dy) p ff) = pr1 ff.
Proof.
  refine (pr1_transportf (A := C⟦_, _⟧) _ _ @ _).
  rewrite transportf_const.
  reflexivity.
Qed.

Proposition transportb_display_map
  {C : category} {D : display_map_class C}
  {x y : C} {dx : display_map_cat_data D x} {dy : display_map_cat_data D y}
  {f g : x --> y}
  (p : g = f) (ff : dx -->[f] dy)
  : pr1 (transportb (mor_disp dx dy) p ff) = pr1 ff.
Proof.
  exact (transportf_display_map _ _).
Qed.

Definition eq_display_map_cat_mor
  {C : category} {D : display_map_class C}
  {x y : C} {dx : display_map_cat_data D x} {dy : display_map_cat_data D y}
  {f : x --> y} {ff gg : dx -->[f] dy}
  (p :  pr1 ff = pr1 gg)
  : ff = gg.
Proof.
  use subtypePath.
  - exact (λ _, homset_property _ _ _ _ _).
  - exact p.
Qed.

Definition display_map_cat_axioms {C : category} {D : display_map_class C}
  : disp_cat_axioms C (display_map_cat_data D).
Proof.
  use tpair; try (use tpair); try (use tpair); intros; cbn in *.
  - use eq_display_map_cat_mor; cbn.
    rewrite transportb_display_map with (ff := ff).
    exact (id_left _).
  - use eq_display_map_cat_mor; cbn.
    rewrite transportb_display_map with (ff := ff).
    exact (id_right _).
  - use eq_display_map_cat_mor.
    rewrite transportb_display_map with (ff := (pr1 ff · pr1 gg · pr1 hh ,, _)).
    exact (assoc _ _ _).
  - intros. apply isaset_total2.
    + exact (homset_property _ _ _).
    + intros. apply isasetaprop. exact (homset_property _ _ _ _ _).
Qed.

Definition display_map_cat {C : category} (D : display_map_class C) : disp_cat C
  := (display_map_cat_data D ,, display_map_cat_axioms).

Definition display_map_pullback
  {C : category} {D : display_map_class C}
  {Γ Γ' : C} (f : Γ' --> Γ)
  (d : display_map_cat D Γ)
  := pr2 D _ _ _ f (pr12 d) (pr22 d).

(** Proof that [display_map_cat] is a [cleaving]. *)
Definition display_map_cartesian_candidate
  {C : category} {D : display_map_class C}
  {Γ Γ' : C} (f : Γ' --> Γ)
  (d : display_map_cat D Γ)
  : ∑ (d' : display_map_cat D Γ'), d' -->[f] d.
Proof.
  use tpair.
  - use tpair.
    + exact (PullbackObject (pr1 (display_map_pullback f d))).
    + exact (PullbackPr2 (pr1 (display_map_pullback f d)) ,, (pr2 (display_map_pullback f d))).
  - use tpair.
    + exact (PullbackPr1 (pr1 (display_map_pullback f d))).
    + cbn. exact (PullbackSqrCommutes (pr1 (display_map_pullback f d))).
Defined.

Definition display_map_is_cartesian
  {C : category} {D : display_map_class C}
  {Γ Γ' : C} (f : Γ' --> Γ)
  (d : display_map_cat D Γ)
  : is_cartesian (pr2 (display_map_cartesian_candidate f d)).
Proof.
  intros Γ'' g d'' [t Ht].
  use tpair.
  - use tpair.
    + exists ((PullbackArrow (pr1 (display_map_pullback f d)) (pr1 d'') t (pr12 d'' · g) (Ht @ assoc _ _ _))).
      simpl. exact (PullbackArrow_PullbackPr2 _ _ _ _ _).
    + simpl. use subtypePath.
      { exact (λ _, homset_property _ _ _ _ _). }
      { simpl. exact (PullbackArrow_PullbackPr1 _ _ _ _ _). }
  - simpl. intros [[p Hp] Hcomp]. use subtypePath.
    + intros [p' Hp'].
      exact (homsets_disp (g · f) d'' _ _ (t,,Ht)).
    + simpl. use subtypePath.
      { exact (λ _, homset_property _ _ _ _ _). }
      {
        simpl. apply PullbackArrowUnique'.
        - apply base_paths in Hcomp. simpl in Hcomp. exact Hcomp.
        - exact Hp.
      }
Defined.

Definition display_map_cleaving
  {C : category} {D : display_map_class C}
  : cleaving (display_map_cat D).
Proof.
  intros Γ Γ' f d.
  exists (pr1 (display_map_cartesian_candidate f d)).
  exists (pr2 (display_map_cartesian_candidate f d)).
  exact (display_map_is_cartesian f d).
Defined.

(** ** Inclusion Functor *)

Definition display_map_inclusion
  {C : category} (D : display_map_class C)
  : disp_functor (functor_identity C) (display_map_cat D) (disp_codomain C).
Proof.
  use tpair; use tpair; simpl.
  - exact (λ _ d, pr1 d ,, pr12 d).
  - exact (λ _ _ _ _ _ ff, ff).
  - simpl. intros x dx. use eq_display_map_cat_mor.
    reflexivity.
  - simpl. intros x y z dx dy dz f g ff gg. use eq_display_map_cat_mor.
    reflexivity.
Defined.
Notation "'ι'" := display_map_inclusion.

Definition ι_preserves_cartesian
  {C : category} {D : display_map_class C}
  : ∏ (c c' : C) (f : c' --> c) (d : display_map_cat D c),
  is_cartesian (♯ (ι D) (display_map_cleaving c c' f d)).
Proof.
  intros x y f dx.
  apply cartesian_iff_isPullback.
  simpl.
  apply isPullback_Pullback.
Qed.

(** ** Map of DispMaps *)
Definition preserves_maps {C C' : category} (D : display_map_class C) (D' : display_map_class C') (F : C ⟶ C') :=
  ∏ (a b : C) (d : a --> b), D d -> D' (#F d).

Definition preserves_pullbacks {C C' : category} (D : display_map_class C) (D' : display_map_class C') (F : C ⟶ C') :=
  ∏ (a b c : C) (f : b --> a) (g : c --> a), D g -> Pullback f g -> Pullback (#F f) (#F g).

Definition map_dispmap {C C' : category} (D : display_map_class C) (D' : display_map_class C') :=
  ∑ (F: C ⟶ C'), preserves_maps D D' F × preserves_pullbacks D D' F.

Definition functor_from_map {C C' : category} (D : display_map_class C) (D' : display_map_class C') (F : map_dispmap D D') : C ⟶ C' := pr1 F.
Coercion functor_from_map : map_dispmap >-> functor.


(** ** Conversion to a Comprehension Category *)
Definition display_map_to_comprehension_category
  {C : category}
  (D : display_map_class C)
  :
  comprehension_cat_structure C.
Proof.
  use make_comprehension_cat_structure.
  - exact (display_map_cat D).
  - exact display_map_cleaving.
  - exact (ι D).
  - exact ι_preserves_cartesian.
Defined.
Notation "'τ'" := display_map_to_comprehension_category.

(** ** Conversion of Maps *)
(** *** Define how functor `F` acts on the Display Map Category  *)
(** Here, we once again follow the definitions for codomain from [Codomain/CodFunctor.v]. *)
Definition display_map_functor_data
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : map_dispmap D₁ D₂)
  : disp_functor_data F (display_map_cat D₁) (display_map_cat D₂).
Proof.
  simple refine (_ ,, _).
  - exact (λ x yf, F (pr1 yf) ,, #F (pr12 yf) ,, pr12 F _ _ _ (pr22 yf)).
  - refine (λ x₁ x₂ yf₁ yf₂ g hp, #F (pr1 hp) ,, _).
    abstract
      (cbn ;
       rewrite <- !functor_comp ;
       apply maponpaths ;
       exact (pr2 hp)).
Defined.

Proposition display_map_functor_axioms
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : map_dispmap D₁ D₂)
  : disp_functor_axioms (display_map_functor_data F).
Proof.
  split.
  - intros x yf.
    use eq_display_map_cat_mor.
    simpl.
    rewrite (@transportb_display_map _ _ _ _ (F (pr1 yf),, # F (pr12 yf),, (pr12 F) (pr1 yf) x (pr12 yf) (pr22 yf))).
    cbn.
    rewrite functor_id.
    apply idpath.
  - intros x₁ x₂ y₃ yf₁ yf₂ yf₃ f₁ f₂ gp₁ gp₂.
    use eq_display_map_cat_mor.
    simpl.
    rewrite (@transportb_display_map _ _ _ _ (F (pr1 yf₁),, # F (pr12 yf₁),, (pr12 F) (pr1 yf₁) x₁ (pr12 yf₁) (pr22 yf₁))).
    cbn.
    rewrite functor_comp.
    apply idpath.
Qed.

Definition display_map_functor
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : map_dispmap D₁ D₂)
  : disp_functor F (display_map_cat D₁) (display_map_cat D₂).
Proof.
  simple refine (_ ,, _).
  - exact (display_map_functor_data F).
  - exact (display_map_functor_axioms F).
Defined.

Definition ι_map_is_map_ι
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : map_dispmap D₁ D₂)
  : disp_nat_z_iso
      (disp_functor_composite (display_map_functor F) (π_χ (τ D₂)))
      (disp_functor_composite (π_χ (τ D₁)) (disp_codomain_functor F))
    (nat_z_iso_id F).
Proof.
  repeat (use tpair); simpl.
  - intros x dx. exact (id_disp (display_map_functor F _ dx)).
  - intros y x f dy dx ff. simpl.
    use subtypePath.
    + exact (λ _, homset_property _ _ _ _ _).
    + rewrite transportb_cod_disp.
      simpl. rewrite id_left. rewrite id_right.
      reflexivity.
  - intros x dx. repeat (use tpair); cbn.
    + exact (identity (F (pr1 dx))).
    + rewrite id_left. rewrite id_right. reflexivity.
    + use subtypePath.
      * exact (λ _, homset_property _ _ _ _ _).
      * rewrite transportb_cod_disp. cbn.
        exact (id_left _).
    + use subtypePath.
      * exact (λ _, homset_property _ _ _ _ _).
      * rewrite transportb_cod_disp. cbn.
        exact (id_left _).
Defined.

Definition map_display_map_to_pseudo_map_structure
  {C C': category}
  {D : display_map_class C} {D' : display_map_class C'}
  (F : map_dispmap D D')
  : pseudo_map_structure (τ D) (τ D').
Proof.
  use make_pseudo_map_structure.
  - exact F.
  - exact (display_map_functor F).
  - exact (ι_map_is_map_ι F).
Defined.
Notation "'≻'" := map_display_map_to_pseudo_map_structure.

Definition nat_trans_to_transformation_structure
  {C C' : category}
  {D : display_map_class C} {D' : display_map_class C'}
  {F F' : map_dispmap D D'}
  (α : nat_trans F F')
  : transformation_structure (≻ F) (≻ F').
Admitted.
