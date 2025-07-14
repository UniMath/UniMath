(*******************************************************************************************

 Category of paired functors between posetal fibrations

 As part of "Weakest Precondition in Fibrations" (https://doi.org/10.1016/j.entcs.2020.09.002),
 the notion of fibered functors allows us to depict effects and their liftings to a predicate category
 as objects in the category Pos-Fib.

 Contents:
  1. Lax slice displayed category
  2. Pos-Fib for the domain fibation

 TODO: Implement a more general version (2-category, where 0-cells are posetal fibrations).
 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.TotalCategory.
Require Import UniMath.CategoryTheory.GrothendieckConstruction.Projection.
Require Import UniMath.MoreFoundations.All.

Local Open Scope cat.

Section PosFib.
Context (C : category)
        (Ω : C)
        (leq : ∏ X : ob C, C⟦X, Ω⟧ → C⟦X, Ω⟧ → hProp)
        (is_po_leq : ∏ X : ob C, isPartialOrder (leq X))
        (is_precomp_monotone_leq :  ∏ (X Y : ob C) (f : C⟦X, Y⟧)
        (g h : C⟦Y, Ω⟧),
        leq Y g h → leq X (g ∘ f) (h ∘ f)).

Definition lax_slice_ob_mor : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - exact (λ X, C⟦X,Ω⟧).
  - exact (λ X Y i j h, leq X i (h · j)).
Defined.


Definition lax_slice_id_comp : disp_cat_id_comp C lax_slice_ob_mor.
Proof.
  split.
  - intros. simpl. rewrite id_left. apply is_po_leq.
  - simpl. intros. destruct (is_po_leq x) as [[trans _] _]. apply trans with (x2 := f · yy).
    + apply X.
    + rewrite assoc'. apply is_precomp_monotone_leq. apply X0.
Defined. 

Definition lax_slice_data : disp_cat_data C := 
  (lax_slice_ob_mor,, lax_slice_id_comp).

Definition lax_slice_axioms : disp_cat_axioms C lax_slice_data.
Proof.
  repeat apply tpair; intros;
  try (apply proofirrelevance, pr2).
  apply isasetaprop, pr2.
Defined.

Definition lax_slice_disp : disp_cat C := 
  (lax_slice_data,, lax_slice_axioms).

Definition lax_slice_cleaving : cleaving lax_slice_disp.
Proof.
  intros c' c f d. use tpair.
  - exact (f · d).
  - use tpair.
    + apply (is_po_leq c).
    + simpl. intros e ff' d'' hh. use iscontraprop1. 
      * apply iscontraprop1.
        ** apply isapropisaprop. 
        ** apply isofhleveltotal2.
          *** exact (pr2 (leq e d'' (ff' · (f · d)))).
          *** intros. simpl. intros. apply (isofhlevelcontr 2).
          exists hh. intros. apply proofirrelevance. apply pr2.
      * simpl. simpl in hh.
        exists (transportf (λ z, leq e d'' z) (assoc'  ff' f d) hh).
        apply proofirrelevance, pr2.
Defined.

Let proj_funct : functor (total_category lax_slice_disp) C := pr1_category lax_slice_disp.


Definition pos_fib_object : UU :=
∑ (F    : functor C C)
(Fdot :  disp_functor F lax_slice_disp lax_slice_disp),
preserves_cleaving lax_slice_cleaving lax_slice_cleaving Fdot.

Definition pos_fib_mor (F G : pos_fib_object) : UU :=
∑ (α : nat_trans (pr1 F) (pr1 G)) 
(α_dot : disp_nat_trans α (pr12 F) (pr12 G)),
∏ (x : C) (X : lax_slice_disp x),
let src := ((pr1 F) x,, (pr12 F) x X) in
let tgt := ((pr1 G) x,, (pr12 G) x X) in
# proj_funct ((α x,, α_dot x X) : total_category lax_slice_disp ⟦ src, tgt ⟧) =
    α (proj_funct ((x,, X))).

Definition pos_fib_id (F : pos_fib_object) : pos_fib_mor F F.
Proof.
exists (nat_trans_id (pr1 F)), (disp_nat_trans_id (pr12 F)). intros. apply idpath.
Defined.

Definition pos_fib_comp {F G H : pos_fib_object}
            (α : pos_fib_mor F G) (β : pos_fib_mor G H) : pos_fib_mor F H.
Proof.
 set (α₁ := pr1 α).
 set (α₂ := pr1 (pr2 α)).
 set (β₁ := pr1 β).
 set (β₂ := pr1 (pr2 β)).
 exists (nat_trans_comp _ _ _ α₁ β₁), (disp_nat_trans_comp α₂ β₂). intros. apply idpath.
Defined.

Definition pos_fib_precat_ob_mor : precategory_ob_mor
 :=
  make_precategory_ob_mor pos_fib_object pos_fib_mor.

Definition pos_fib_precat_data : precategory_data.
Proof.
  use make_precategory_data.
  - exact pos_fib_precat_ob_mor.
  - exact pos_fib_id.
  - intros a b c f g. exact (pos_fib_comp f g).
Defined.

Proposition isaprop_disp_nat_trans (a b : pos_fib_object) (α : nat_trans (pr1 a) (pr1 b)) (α_dot : disp_nat_trans α (pr12 a) (pr12 b)) : isaprop (∑ _ : disp_nat_trans α (pr12 a) (pr12 b),
∏ x : C, C ⟦ x, Ω ⟧ → α x = α x).
Proof.
apply isapropdirprod.
    + unfold disp_nat_trans. unfold disp_nat_trans_data. apply  isofhleveltotal2.
      * do 2 (apply impred; intro). simpl. apply isapropifcontr. apply iscontraprop1. apply pr2.
      apply ((pr1 α_dot) t t0).
      * simpl. intros l x y. apply isapropifcontr. apply iscontraprop1. simpl in *. 
      set (D_a := disp_functor_data_from_disp_functor (pr12 a)).
            set (D_b := disp_functor_data_from_disp_functor (pr12 b)).
            change (disp_nat_trans_data α D_a D_b) in l. apply (isaprop_disp_nat_trans_axioms α l). exact x.
    + apply impred_isaprop. intro. apply impred_isaprop. intro. apply C.
Defined.

Lemma pos_fib_id_left (a b : pos_fib_object) (f : pos_fib_mor a b) :
  pos_fib_comp (pos_fib_id a) f = f.
Proof.
  destruct f as [α [α_dot law]]. simpl. unfold pos_fib_comp. simpl. use total2_paths_f.
  - simpl. apply nat_trans_eq. apply (pr2 C). intros. simpl. apply id_left.
  - apply proofirrelevance. simpl. apply isaprop_disp_nat_trans. exact α_dot.
Defined.

Lemma pos_fib_id_right (a b : pos_fib_object) (f : pos_fib_mor a b) :
  pos_fib_comp f (pos_fib_id b) = f.
Proof.
  destruct f as [α [α_dot law]]. simpl. unfold pos_fib_comp. simpl. use total2_paths_f.
  - simpl. apply nat_trans_eq. apply (pr2 C). intros. simpl. apply id_right.
  - apply proofirrelevance. simpl. apply isaprop_disp_nat_trans. exact α_dot.
Defined.

Lemma pos_fib_comp_assoc (a b c d : pos_fib_object) (f : pos_fib_mor a b)
(g : pos_fib_mor b c) (h : pos_fib_mor c d) :
  pos_fib_comp f (pos_fib_comp g h) = pos_fib_comp (pos_fib_comp f g) h.
Proof.
use total2_paths_f.
- simpl. apply nat_trans_comp_assoc. apply (pr2 C).
- apply proofirrelevance. simpl. apply isapropdirprod.
  + unfold disp_nat_trans. simpl. apply isofhleveltotal2.
    * do 2 (apply impred; intro). simpl. apply isapropifcontr. apply iscontraprop1. apply pr2. 
    eapply (pr11 (is_po_leq (pr1 a t))). exact (pr12 f t t0).
    eapply (pr11 (is_po_leq (pr1 a t))).  apply is_precomp_monotone_leq. exact (pr12 g t t0).
    eapply (pr11 (is_po_leq (pr1 a t))). apply is_precomp_monotone_leq. apply is_precomp_monotone_leq. exact (pr12 h t t0).
    do 2 (rewrite assoc). apply (is_po_leq (pr1 a t)).
    * intros. simpl. intros. apply isapropifcontr. apply iscontraprop1.   set (D_a := disp_functor_data_from_disp_functor (pr12 a)).
    set (D_d := disp_functor_data_from_disp_functor (pr12 d)).
    change (disp_nat_trans_data (λ x : C, pr1 f x · pr1 g x · pr1 h x) D_a D_d) in x. apply (isaprop_disp_nat_trans_axioms
    (nat_trans_comp _ _ _ (nat_trans_comp _ _ _ (pr1 f) (pr1 g)) (pr1 h))
    x). exact x0.
+ apply impred_isaprop. intro. apply impred_isaprop. intro. apply C.
Defined.

Lemma pos_fib_comp_assoc' (a b c d : pos_fib_object) (f : pos_fib_mor a b)
(g : pos_fib_mor b c) (h : pos_fib_mor c d) :
  pos_fib_comp (pos_fib_comp f g) h = pos_fib_comp f (pos_fib_comp g h).
Proof.
  use total2_paths_f.
  - simpl. apply nat_trans_comp_assoc'. apply (pr2 C).
  - apply proofirrelevance. simpl. apply isapropdirprod.
    + unfold disp_nat_trans. simpl. apply isofhleveltotal2.
      * do 2 (apply impred; intro). simpl. apply isapropifcontr. apply iscontraprop1. apply pr2. 
      eapply (pr11 (is_po_leq (pr1 a t))). exact (pr12 f t t0).
      eapply (pr11 (is_po_leq (pr1 a t))).  apply is_precomp_monotone_leq. exact (pr12 g t t0).
      eapply (pr11 (is_po_leq (pr1 a t))). apply is_precomp_monotone_leq. apply is_precomp_monotone_leq. exact (pr12 h t t0).
      do 2 (rewrite assoc'). apply (is_po_leq (pr1 a t)).
      * intros. simpl. intros. apply isapropifcontr. apply iscontraprop1.  set (D_a := disp_functor_data_from_disp_functor (pr12 a)).
      set (D_d := disp_functor_data_from_disp_functor (pr12 d)).
      change (disp_nat_trans_data (λ x : C, pr1 f x · (pr1 g x · pr1 h x)) D_a D_d) in x. apply (isaprop_disp_nat_trans_axioms
      (nat_trans_comp _ _ _ (pr1 f) (nat_trans_comp _ _ _ (pr1 g) (pr1 h)))
      x). exact x0.
  + apply impred_isaprop. intro. apply impred_isaprop. intro. apply C.
Defined.

Proposition is_precategory_pos_fib : is_precategory pos_fib_precat_data.
Proof.
  repeat split;cbn.
  - apply pos_fib_id_left.
  - apply pos_fib_id_right.
  - apply pos_fib_comp_assoc.
  - apply pos_fib_comp_assoc'.
Defined.

Definition pos_fib_precat : precategory.
Proof.
  use make_precategory.
  - exact pos_fib_precat_data.
  - exact is_precategory_pos_fib.
Defined.

Definition pos_fib_cat : category.
Proof.
  exists pos_fib_precat.
  unfold has_homsets. intros. apply isaset_total2.
  - apply isaset_nat_trans. apply C.
  - intros. apply isaset_total2.
    + apply isaset_disp_nat_trans.
    + intros. apply isasetaprop. do 2 (apply impred_isaprop; intros). apply homset_property.
Defined.