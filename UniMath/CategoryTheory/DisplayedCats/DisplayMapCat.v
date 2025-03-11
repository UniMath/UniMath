(** * Display Map Category
    Contents:
    - add display map as a subclass of morphisms [display_map_class C]
    - add an interpretation as a subcategory of [codomain C]
    - show that this subcategory is a cleaving [display_map_cleaving]
    - define the inclusion functor [ι : display_map_cat D ⇒ disp_codomain C]
    - define the map between display maps [map_dispmap D D']
    - show that given a Display Map Category we can construct a corresponding Comprehension Category
    - show that given a functor between display map categories, we can construct a pseudo map between the corresponding comprehension categories
    - show the same for natural transformations
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Local Open Scope cat.
Local Open Scope comp_cat_struct.

Declare Scope disp_map_cat.
Local Open Scope disp_map_cat.


(** ** Display Map *)
Definition display_map_class_data (C : category) : UU :=
  ∏ a b : C, a --> b -> hProp.
Definition display_map_class_data_to_fun {C} {a b} (D : display_map_class_data C) : a --> b -> hProp := D a b.
Coercion display_map_class_data_to_fun : display_map_class_data >-> Funclass.

Definition has_map_pullbacks {C : category} (D : display_map_class_data C) : UU :=
  ∏ (a b c : C) (f : b --> a) (d : c --> a),
    D _ _ d -> ∑ (p : Pullback d f), D _ _ (PullbackPr2 p).

Definition display_map_class (C : category) : UU :=
  ∑ (D : display_map_class_data C), has_map_pullbacks D.

Definition display_map_class_to_data {C : category} (D : display_map_class C) : display_map_class_data C := pr1 D.
Coercion display_map_class_to_data : display_map_class >-> display_map_class_data.

Definition isPredicate_display_map_class
  {C : category} (D : display_map_class C)
  (a b : C)
  : isPredicate (pr1 D a b).
Proof.
  intros f. apply (pr2 (pr1 D a b f)).
Qed.

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
  - intros x xx.
    exists (identity (pr1 xx)).
    abstract (rewrite id_left, id_right; reflexivity ).
  - intros x y z f g xx yy zz ff gg.
    exists (pr1 ff · pr1 gg).
    abstract (
      rewrite <- assoc; rewrite (pr2 gg), assoc, (pr2 ff);
      symmetry; exact (assoc _ _ _)).
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

(** Bit of univalence *)
Lemma is_univalent_display_map_cat
  {C : category} (C_univ : is_univalent C)
  (D : display_map_class C)
  : is_univalent_disp (display_map_cat D).
Proof.
  intros x₁ x₂ px12 dx₁ dx₂ d_iso; cbn.
  unfold iscontr, hfiber.
  use tpair; try (use tpair); cbn.
  - use total2_paths_f; cbn.
    + rewrite pr1_transportf, transportf_const; cbn.
      apply (isotoid _ C_univ).
      exists (pr11 d_iso), (pr112 d_iso). split.
      * pose (Hfg := pr22 (is_z_iso_disp_from_z_iso d_iso)). apply base_paths in Hfg.
        unfold mor_disp in Hfg. simpl in Hfg.
        rewrite pr1_transportb, transportb_const in Hfg.  simpl in Hfg.
        exact Hfg.
      * pose (Hgf := pr12 (is_z_iso_disp_from_z_iso d_iso)). apply base_paths in Hgf.
        unfold mor_disp in Hgf. simpl in Hgf.
        rewrite pr1_transportb, transportb_const in Hgf.  simpl in Hgf.
        exact Hgf.
    + admit.
  - admit.
Admitted.

Definition univalent_display_map_cat
  {C : category} (C_univ : is_univalent C)
  (D : display_map_class C)
  : disp_univalent_category C.
Proof.
  use make_disp_univalent_category.
  - exact (display_map_cat D).
  - exact (is_univalent_display_map_cat C_univ D).
Defined.

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
      exact (PullbackArrow_PullbackPr2 _ _ _ _ _).
    + simpl. use subtypePath.
      abstract ( exact (λ _, homset_property _ _ _ _ _)).
      exact (PullbackArrow_PullbackPr1 _ _ _ _ _).
  - simpl. intros [[p Hp] Hcomp]. use subtypePath.
    abstract ( intros [p' Hp']; exact (homsets_disp (g · f) d'' _ _ (t,,Ht))).
    use subtypePath.
    abstract ( exact (λ _, homset_property _ _ _ _ _)).
    simpl. apply PullbackArrowUnique'.
    + apply base_paths in Hcomp. simpl in Hcomp. exact Hcomp.
    + exact Hp.
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
Notation "'ι'" := display_map_inclusion : disp_map_cat.

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

Lemma is_cartesian_ι
  {C : category} (D : display_map_class C)
  : is_cartesian_disp_functor (ι D).
Proof.
  apply (cartesian_functor_from_cleaving display_map_cleaving).
  exact (ι_preserves_cartesian).
Qed.

Definition cartesian_ι
  {C : category} (D : display_map_class C)
  : cartesian_disp_functor (functor_identity C) (display_map_cat D) (disp_codomain C)
  := (ι D ,, is_cartesian_ι D).

Lemma ι_ff
  {C : category} (D : display_map_class C)
  : disp_functor_ff (ι D).
Proof.
  intros x₁ x₂ dx₁ dx₂ f [ι_g Hsq].
  unfold iscontr, hfiber.
  assert (Heq : (♯(ι D))%mor_disp (ι_g ,, Hsq) = (ι_g,,Hsq)).
  {
    cbn. exact (idpath _).
  }
  exists ((ι_g ,, Hsq) ,, Heq).
  intros [[g' Hsq'] Heq'].
  use subtypePath.
  - intros t. exact (homsets_disp _ _ _ _ _).
  - cbn. exact Heq'.
Qed.

(** ** Functor between Display Map Classes *)

Definition preserves_maps {C C' : category} (D : display_map_class C) (D' : display_map_class C') (F : C ⟶ C') :=
  ∏ (a b : C) (d : a --> b), D d -> D' (#F d).

Definition preserves_pullbacks {C C' : category} (D : display_map_class C) (D' : display_map_class C') (F : C ⟶ C') :=
  ∏ (a b c : C) (f : b --> a) (g : c --> a) (_ : D f) (pb : Pullback f g), isPullback (!functor_comp F _ _ @ maponpaths (#F) (PullbackSqrCommutes pb) @ functor_comp F _ _).

Definition display_map_class_functor {C C' : category} (D : display_map_class C) (D' : display_map_class C') :=
  ∑ (F: C ⟶ C'), preserves_maps D D' F × preserves_pullbacks D D' F.

Definition functor_from_display_map_class_functor {C C' : category} (D : display_map_class C) (D' : display_map_class C') (F : display_map_class_functor D D') : C ⟶ C' := pr1 F.
Coercion functor_from_display_map_class_functor : display_map_class_functor >-> functor.

Definition display_map_class_functor_preserved_pullback
  {C₁ C₂ : category} {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : display_map_class_functor D₁ D₂)
  {a b c: C₁} {d : b --> a} {f : c --> a} (H : D₁ d) (pb : Pullback d f)
  : Pullback (#F d) (#F f).
Proof.
  repeat (use tpair).
  - exact (F pb).
  - exact (#F (PullbackPr1 pb)).
  - exact (#F (PullbackPr2 pb)).
  - simpl. exact (!functor_comp F _ _ @ maponpaths (#F) (PullbackSqrCommutes pb) @ functor_comp F _ _).
  - simpl. exact (pr22 F _ _ _ _ _ H pb).
Defined.

Definition display_map_class_functor_identity
  {C : category} (D : display_map_class C)
  : display_map_class_functor D D.
Proof.
  exists (functor_identity C).
  abstract (exact ((λ _ _ _ tt, tt) ,, (λ _ _ _ _ _ _ pb, isPullback_Pullback pb))).
Defined.

Definition display_map_class_functor_composite
  {C₁ C₂ C₃ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂} {D₃ : display_map_class C₃}
  (F₁ : display_map_class_functor D₁ D₂)
  (F₂ : display_map_class_functor D₂ D₃)
  : display_map_class_functor D₁ D₃.
Proof.
  exists (functor_composite F₁ F₂).
  split.
  - abstract (exact (λ _ _ _ tt, (pr12 F₂) _ _ _ ((pr12 F₁) _ _ _ tt))).
  - abstract (
        intros ? ? ? ? ? tt pb; unfold functor_comp; simpl;
        apply ((pr22 F₂) _ _ _ _ _ ((pr12 F₁) _ _ _ tt) (display_map_class_functor_preserved_pullback F₁ tt pb))
      ).
Defined.

(** ** Functor between Display Map Categories *)
(** *** Define how functor `F` acts on the Display Map Category  *)
(** Here, we once again follow the definitions for codomain from [Codomain/CodFunctor.v]. *)
Definition display_map_functor_data
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : display_map_class_functor D₁ D₂)
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
  (F : display_map_class_functor D₁ D₂)
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
  (F : display_map_class_functor D₁ D₂)
  : disp_functor F (display_map_cat D₁) (display_map_cat D₂).
Proof.
  simple refine (_ ,, _).
  - exact (display_map_functor_data F).
  - exact (display_map_functor_axioms F).
Defined.

Lemma isPullback_is_cartesian_display_map
  {C : category} (D : display_map_class C)
  {x₁ x₂ : C} {f : x₁ --> x₂}
  {dx₁ : display_map_cat D x₁} {dx₂ : display_map_cat D x₂} {df : dx₁ -->[f] dx₂}
  : isPullback (pr2 df) -> is_cartesian df.
Proof.
  intros Hpb x₃ g dx₃ dh. unfold isPullback in Hpb. specialize Hpb with (pr1 dx₃) (pr1 dh) (pr12 dx₃ · g).
  pose (pb := Hpb (pr2 dh @ assoc _ _ _)). destruct pb as [[hk [H1 H2]] Hunique].
  repeat (use tpair); simpl in *.
  - exact hk.
  - exact H2.
  - use eq_display_map_cat_mor; cbn. exact H1.
  - intros [[hk' H2'] H1'].
    repeat (use subtypePath).
    + admit.
    + exact (λ _, homset_property _ _ _ _ _).
    + simpl. apply base_paths in H1'. simpl in *.
      specialize Hunique with (hk' ,, (H1' ,, H2')).
      apply base_paths in Hunique. simpl in Hunique.
      exact Hunique.
Admitted.

Lemma is_cartesian_display_map_functor
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : display_map_class_functor D₁ D₂)
  : is_cartesian_disp_functor (display_map_functor F).
Proof.
  apply (cartesian_functor_from_cleaving display_map_cleaving).
  intros x₁ x₂ f dx₁.
  apply isPullback_is_cartesian_display_map.
  apply (pr22 F).
  exact (pr22 dx₁).
Qed.

(** ** Natural Transformation *)
(** Once more we rely on the definition for the codomain display category to define the transformation between two display map categories. *)
Definition display_map_nat_trans
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  {F G : display_map_class_functor D₁ D₂}
  (α : F ⟹ G)
  : disp_nat_trans α (display_map_functor F) (display_map_functor G).
Proof.
  simple refine (_ ,, _).
  - refine (λ y xf, α _ ,, _).
    abstract
      (cbn ;
       apply (!(nat_trans_ax α _ _ _))).
  - abstract (intros y₁ y₂ g xf₁ xf₂ p ;
       use eq_display_map_cat_mor ;
       rewrite (@transportb_display_map _ _ _ _ (display_map_functor F y₁ xf₁)) ;
       apply (nat_trans_ax α _ _ _)).
Defined.

(** ** Corresponding Comprehension Category *)
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
Notation "'DM2CC'" := display_map_to_comprehension_category : disp_map_cat.

(** ** Pseudo Map corresponding to a functor between Display Map Categories *)
Definition map_ι_is_ι_map
  {C₁ C₂ : category}
  {D₁ : display_map_class C₁} {D₂ : display_map_class C₂}
  (F : display_map_class_functor D₁ D₂)
  : disp_nat_z_iso
      (disp_functor_composite (π_χ (DM2CC D₁)) (disp_codomain_functor F))
      (disp_functor_composite (display_map_functor F) (π_χ (DM2CC D₂)))
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
  (F : display_map_class_functor D D')
  : pseudo_map_structure (DM2CC D) (DM2CC D').
Proof.
  use make_pseudo_map_structure.
  - exact F.
  - exact (display_map_functor F).
  - exact (map_ι_is_ι_map F).
Defined.
Notation "'MD2PM'" := map_display_map_to_pseudo_map_structure : disp_map_cat.

(** ** Transformation corresponding to a natural transformation between functors between display map categories *)

Definition nat_trans_to_transformation_structure_axiom
  {C C' : category}
  {D : display_map_class C} {D' : display_map_class C'}
  {F F' : display_map_class_functor D D'}
  (α : nat_trans F F')
  : @transformation_structure_axiom _ _ _ _ (MD2PM F) (MD2PM F') α (display_map_nat_trans α).
Proof.
  intros x xx.
  use eq_cod_mor.
  rewrite transportb_cod_disp.
  simpl.
  rewrite id_left,id_right.
  exact (idpath _).
Qed.

Definition nat_trans_to_transformation_structure
  {C C' : category}
  {D : display_map_class C} {D' : display_map_class C'}
  {F F' : display_map_class_functor D D'}
  (α : nat_trans F F')
  : transformation_structure (MD2PM F) (MD2PM F').
Proof.
  use (_ ,, _ ,, _); cbn.
 - exact α.
 - exact (display_map_nat_trans α).
 - exact (nat_trans_to_transformation_structure_axiom _).
Defined.
