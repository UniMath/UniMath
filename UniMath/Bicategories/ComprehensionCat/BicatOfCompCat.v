(************************************************************************************

 The bicategory of full comprehension categories

 In this file, we construct the bicategory of comprehension categories, and we prove
 that this bicategory is univalent. To do so, we use displayed bicategories. We take
 the following steps.
 - We define the displayed bicategory [disp_bicat_cat_with_terminal_disp_cat] over
   the bicategory of categories. This one adds a displayed category and a terminal
   object. It is defined by taking a product of displayed bicategories.
 - After that, we take a subbicategory ([disp_bicat_cat_with_terminal_cleaving]) of
   which the objects are equipped with a cleaving and of which the morphisms are
   cartesian functors.
 - Next we add a comprehension functor ([disp_bicat_cat_terminal_cleaving_functor]).
   This displayed bicategory is defined by hand and we do not use a more general
   construction for it.
 - Finally, we take a full subbicategory ([disp_bicat_comp_cat]) of which the objects
   are full comprehension categories, so we require the comprehension functor to be
   both fully faithful and cartesian.

 It is important to note that we do not use any sigma-construction in the intermediate
 steps. The resulting displayed bicategory is thus not over the bicategory of univalent
 categories. The reason for this choice, is because it allows a nice proof of univalence
 for this bicategory. Using sigmas would make this more complicated, because the
 statements about the univalence of sigma constructions assume that the displayed
 2-cells are invertible and propositions (which does not hold in the first step,
 because in that step, we add a displayed category).

 In addition, we look at morphisms that preserve all structure up to isomorphism
 rather than up to a 2-cell. The invertibility condition is added in the final step,
 so in [disp_bicat_full_comp_cat], and this step is constructed using a subbicategory
 rather than a full subbicategory. As such, in [disp_bicat_cat_terminal_cleaving_functor],
 the displayed 1-cells only preserve the structure up to a 2-cell. Furthermore, we
 define a univalent bicategory of full comprehension categories instead of arbitrary
 comprehension category.

 We also provide accessors and builders for the objects, 1-cells, and 2-cells in
 every step.

 Sources:
 - Categorical Logic and Type Theory, by Bart Jacobs

 Contents
 1. Bicategories of categories with a terminal object and a displayed category
 2. Bicategories of categories with a terminal object and a fibration
 3. Bicategory of categories with a comprehension structure
 4. Bicategory of full comprehension categories

 ************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.

Local Open Scope cat.

(** * 1. Bicategories of categories with a terminal object and a displayed category *)
Definition disp_bicat_cat_with_terminal_disp_cat
  : disp_bicat bicat_of_univ_cats
  := disp_dirprod_bicat
       disp_bicat_terminal_obj
       disp_bicat_of_univ_disp_cats.

Proposition disp_univalent_2_1_disp_bicat_cat_with_terminal_disp_cat
  : disp_univalent_2_1 disp_bicat_cat_with_terminal_disp_cat.
Proof.
  use is_univalent_2_1_dirprod_bicat.
  - exact disp_univalent_2_1_disp_bicat_terminal_obj.
  - exact disp_univalent_2_1_disp_bicat_of_univ_disp_cat.
Qed.

Proposition disp_univalent_2_0_disp_bicat_cat_with_terminal_disp_cat
  : disp_univalent_2_0 disp_bicat_cat_with_terminal_disp_cat.
Proof.
  use is_univalent_2_0_dirprod_bicat.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_disp_bicat_terminal_obj.
  - split.
    + exact disp_univalent_2_0_disp_bicat_of_univ_disp_cat.
    + exact disp_univalent_2_1_disp_bicat_of_univ_disp_cat.
Qed.

Definition bicat_cat_with_terminal_disp_cat
  : bicat
  := total_bicat disp_bicat_cat_with_terminal_disp_cat.

Proposition is_univalent_2_1_bicat_cat_with_terminal_disp_cat
  : is_univalent_2_1 bicat_cat_with_terminal_disp_cat.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_cat_with_terminal_disp_cat.
Qed.

Proposition is_univalent_2_0_bicat_cat_with_terminal_disp_cat
  : is_univalent_2_0 bicat_cat_with_terminal_disp_cat.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact disp_univalent_2_0_disp_bicat_cat_with_terminal_disp_cat.
Qed.

Proposition is_univalent_2_bicat_cat_with_terminal_disp_cat
  : is_univalent_2 bicat_cat_with_terminal_disp_cat.
Proof.
  split.
  - exact is_univalent_2_0_bicat_cat_with_terminal_disp_cat.
  - exact is_univalent_2_1_bicat_cat_with_terminal_disp_cat.
Qed.

Definition cat_with_terminal_disp_cat
  : UU
  := bicat_cat_with_terminal_disp_cat.

Definition make_cat_with_terminal_disp_cat
           (C : univalent_category)
           (T : Terminal C)
           (D : disp_univalent_category C)
  : cat_with_terminal_disp_cat
  := C ,, (T ,, tt) ,, D.

Coercion cat_of_cat_with_terminal_disp_cat
         (C : cat_with_terminal_disp_cat)
  : univalent_category
  := pr1 C.

Definition empty_context
           (C : cat_with_terminal_disp_cat)
  : Terminal C
  := pr112 C.

Definition disp_cat_of_types
           (C : cat_with_terminal_disp_cat)
  : disp_univalent_category C
  := pr22 C.

Definition functor_with_terminal_disp_cat
           (C₁ C₂ : cat_with_terminal_disp_cat)
  : UU
  := C₁ --> C₂.

Definition make_functor_with_terminal_disp_cat
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F : C₁ ⟶ C₂)
           (HF : preserves_terminal F)
           (FF : disp_functor F (disp_cat_of_types C₁) (disp_cat_of_types C₂))
  : functor_with_terminal_disp_cat C₁ C₂
  := F ,, (tt ,, HF) ,, FF.

Coercion functor_of_functor_with_terminal_disp_cat
         {C₁ C₂ : cat_with_terminal_disp_cat}
         (F : functor_with_terminal_disp_cat C₁ C₂)
  : C₁ ⟶ C₂
  := pr1 F.

Definition comp_cat_type_functor
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F : functor_with_terminal_disp_cat C₁ C₂)
  : disp_functor F (disp_cat_of_types C₁) (disp_cat_of_types C₂)
  := pr22 F.

Definition comp_cat_functor_terminal
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F : functor_with_terminal_disp_cat C₁ C₂)
  : preserves_terminal F
  := pr212 F.

Definition nat_trans_with_terminal_disp_cat
           {C₁ C₂ : cat_with_terminal_disp_cat}
           (F G : functor_with_terminal_disp_cat C₁ C₂)
  : UU
  := F ==> G.

Definition make_nat_trans_with_terminal_disp_cat
           {C₁ C₂ : cat_with_terminal_disp_cat}
           {F G : functor_with_terminal_disp_cat C₁ C₂}
           (τ : F ⟹ G)
           (ττ : disp_nat_trans
                   τ
                   (comp_cat_type_functor F)
                   (comp_cat_type_functor G))
  : nat_trans_with_terminal_disp_cat F G
  := τ ,, (tt ,, tt) ,, ττ.

Coercion nat_trans_of_nat_trans_with_terminal_disp_cat
         {C₁ C₂ : cat_with_terminal_disp_cat}
         {F G : functor_with_terminal_disp_cat C₁ C₂}
         (τ : nat_trans_with_terminal_disp_cat F G)
  : F ⟹ G
  := pr1 τ.

Definition comp_cat_type_nat_trans
           {C₁ C₂ : cat_with_terminal_disp_cat}
           {F G : functor_with_terminal_disp_cat C₁ C₂}
           (τ : nat_trans_with_terminal_disp_cat F G)
  : disp_nat_trans τ (comp_cat_type_functor F) (comp_cat_type_functor G)
  := pr22 τ.

(** * 2. Bicategories of categories with a terminal object and a fibration *)
Definition disp_bicat_cat_with_terminal_cleaving
  : disp_bicat bicat_cat_with_terminal_disp_cat.
Proof.
  use disp_subbicat.
  - exact (λ C, cleaving (disp_cat_of_types C)).
  - exact (λ C₁ C₂ D₁ D₂ F, is_cartesian_disp_functor (comp_cat_type_functor F)).
  - intros X fibX x y f xx yy ff p.
    exact p.
  - intros X Y Z F G fibX fibY fibZ cartF cartG x y f xx yy ff p ; simpl.
    apply cartG.
    apply cartF.
    exact p.
Defined.

Proposition disp_univalent_2_1_disp_bicat_cat_with_terminal_cleaving
  : disp_univalent_2_1 disp_bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat_univalent_2_1.
  intros.
  apply isaprop_is_cartesian_disp_functor.
Qed.

Proposition disp_univalent_2_0_disp_bicat_cat_with_terminal_cleaving
  : disp_univalent_2_0 disp_bicat_cat_with_terminal_cleaving.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_cat_with_terminal_disp_cat.
  - intro.
    apply isaprop_cleaving.
    apply disp_univalent_category_is_univalent_disp.
  - intros.
    apply isaprop_is_cartesian_disp_functor.
Qed.

Definition bicat_cat_with_terminal_cleaving
  : bicat
  := total_bicat disp_bicat_cat_with_terminal_cleaving.

Proposition is_univalent_2_1_bicat_cat_with_terminal_cleaving
  : is_univalent_2_1 bicat_cat_with_terminal_cleaving.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_cat_with_terminal_disp_cat.
  - exact disp_univalent_2_1_disp_bicat_cat_with_terminal_cleaving.
Qed.

Proposition is_univalent_2_0_bicat_cat_with_terminal_cleaving
  : is_univalent_2_0 bicat_cat_with_terminal_cleaving.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_cat_with_terminal_disp_cat.
  - exact disp_univalent_2_0_disp_bicat_cat_with_terminal_cleaving.
Qed.

Proposition is_univalent_2_bicat_cat_with_terminal_cleaving
  : is_univalent_2 bicat_cat_with_terminal_cleaving.
Proof.
  split.
  - exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
Qed.

Definition cat_with_terminal_cleaving
  : UU
  := bicat_cat_with_terminal_cleaving.

Definition make_cat_with_terminal_cleaving
           (C : cat_with_terminal_disp_cat)
           (DC : cleaving (disp_cat_of_types C))
  : cat_with_terminal_cleaving
  := C ,, DC ,, tt.

Coercion cat_terminal_disp_cat_of_cat_with_terminal_disp_cat
         (C : cat_with_terminal_cleaving)
  : cat_with_terminal_disp_cat
  := pr1 C.

Definition cleaving_of_types
           (C : cat_with_terminal_cleaving)
  : cleaving (disp_cat_of_types C)
  := pr12 C.

Definition functor_with_terminal_cleaving
           (C₁ C₂ : cat_with_terminal_cleaving)
  : UU
  := C₁ --> C₂.

Definition make_functor_with_terminal_cleaving
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F : functor_with_terminal_disp_cat C₁ C₂)
           (HF : is_cartesian_disp_functor (comp_cat_type_functor F))
  : functor_with_terminal_cleaving C₁ C₂
  := F ,, tt ,, HF.

Coercion functor_terminal_disp_cat_of_functor_with_terminal_cleaving
         {C₁ C₂ : cat_with_terminal_cleaving}
         (F : functor_with_terminal_cleaving C₁ C₂)
  : functor_with_terminal_disp_cat C₁ C₂
  := pr1 F.

Definition is_cartesian_comp_cat_type_functor
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F : functor_with_terminal_cleaving C₁ C₂)
  : is_cartesian_disp_functor (comp_cat_type_functor F)
  := pr22 F.

Definition nat_trans_with_terminal_cleaving
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F G : functor_with_terminal_cleaving C₁ C₂)
  : UU
  := F ==> G.

Definition make_nat_trans_with_terminal_cleaving
           {C₁ C₂ : cat_with_terminal_cleaving}
           {F G : functor_with_terminal_cleaving C₁ C₂}
           (τ : nat_trans_with_terminal_disp_cat F G)
  : nat_trans_with_terminal_cleaving F G
  := τ ,, tt ,, tt.

Coercion nat_trans_with_terminal_disp_cat_of_nat_trans_with_terminal_cleaving
         {C₁ C₂ : cat_with_terminal_cleaving}
         {F G : functor_with_terminal_cleaving C₁ C₂}
         (τ : nat_trans_with_terminal_cleaving F G)
  : nat_trans_with_terminal_disp_cat F G
  := pr1 τ.

(** * 3. Bicategory of categories with a comprehension structure *)
Definition comprehension_functor
           (C : cat_with_terminal_cleaving)
  : UU
  := disp_functor
       (functor_identity C)
       (disp_cat_of_types C)
       (disp_codomain C).

Identity Coercion comprehension_functor_to_disp_functor
  : comprehension_functor >-> disp_functor.

Definition comprehension_functor_ob
           {C : cat_with_terminal_cleaving}
           (χ : comprehension_functor C)
           {x : C}
           (xx : disp_cat_of_types C x)
  : C
  := pr1 (χ x xx).

Definition comprehension_functor_cod_mor
           {C : cat_with_terminal_cleaving}
           (χ : comprehension_functor C)
           {x : C}
           (xx : disp_cat_of_types C x)
  : comprehension_functor_ob χ xx --> x
  := pr2 (χ x xx).

Definition comprehension_functor_mor
           {C : cat_with_terminal_cleaving}
           (χ : comprehension_functor C)
           {x y : C}
           {f : x --> y}
           {xx : disp_cat_of_types C x}
           {yy : disp_cat_of_types C y}
           (ff : xx -->[ f ] yy)
  : comprehension_functor_ob χ xx --> comprehension_functor_ob χ yy
  := pr1 ((♯ χ ff)%mor_disp).

Proposition comprehension_functor_mor_comm
            {C : cat_with_terminal_cleaving}
            (χ : comprehension_functor C)
            {x y : C}
            {f : x --> y}
            {xx : disp_cat_of_types C x}
            {yy : disp_cat_of_types C y}
            (ff : xx -->[ f ] yy)
  : comprehension_functor_mor χ ff · comprehension_functor_cod_mor χ yy
    =
    comprehension_functor_cod_mor χ xx · f.
Proof.
  exact (pr2 ((♯ χ ff)%mor_disp)).
Qed.

Proposition comprehension_functor_mor_id
            {C : cat_with_terminal_cleaving}
            (χ : comprehension_functor C)
            {x : C}
            (xx : disp_cat_of_types C x)
  : comprehension_functor_mor χ (id_disp xx) = identity _.
Proof.
  refine (maponpaths pr1 (disp_functor_id χ xx) @ _) ; cbn.
  apply idpath.
Qed.

Definition comprehension_functor_mor_comp
           {C : cat_with_terminal_cleaving}
           (χ : comprehension_functor C)
           {x y z : C}
           {f : x --> y}
           {g : y --> z}
           {xx : disp_cat_of_types C x}
           {yy : disp_cat_of_types C y}
           {zz : disp_cat_of_types C z}
           (ff : xx -->[ f ] yy)
           (gg : yy -->[ g ] zz)
  : comprehension_functor_mor χ (ff ;; gg)%mor_disp
    =
    comprehension_functor_mor χ ff · comprehension_functor_mor χ gg.
Proof.
  refine (maponpaths pr1 (disp_functor_comp χ ff gg) @ _) ; cbn.
  apply idpath.
Qed.

Definition comprehension_nat_trans
           {C₁ C₂ : cat_with_terminal_cleaving}
           (χ₁ : comprehension_functor C₁)
           (χ₂ : comprehension_functor C₂)
           (F : functor_with_terminal_cleaving C₁ C₂)
  : UU
  := disp_nat_trans
       (nat_trans_id _)
       (disp_functor_composite χ₁ (disp_codomain_functor F))
       (disp_functor_composite (comp_cat_type_functor F) χ₂).

Identity Coercion comprehension_nat_trans_to_disp_nat_trans
  : comprehension_nat_trans >-> disp_nat_trans.

Definition comprehension_nat_trans_mor
           {C₁ C₂ : cat_with_terminal_cleaving}
           {χ₁ : comprehension_functor C₁}
           {χ₂ : comprehension_functor C₂}
           {F : functor_with_terminal_cleaving C₁ C₂}
           (Fχ : comprehension_nat_trans χ₁ χ₂ F)
           {x : C₁}
           (xx : disp_cat_of_types C₁ x)
  : F (comprehension_functor_ob χ₁ xx)
    -->
    comprehension_functor_ob χ₂ (comp_cat_type_functor F x xx)
  := pr1 (Fχ x xx).

Proposition comprehension_nat_trans_mor_comm
            {C₁ C₂ : cat_with_terminal_cleaving}
            {χ₁ : comprehension_functor C₁}
            {χ₂ : comprehension_functor C₂}
            {F : functor_with_terminal_cleaving C₁ C₂}
            (Fχ : comprehension_nat_trans χ₁ χ₂ F)
            (x : C₁)
            (xx : disp_cat_of_types C₁ x)
  : comprehension_nat_trans_mor Fχ xx
    · comprehension_functor_cod_mor χ₂ (comp_cat_type_functor F x xx)
    =
    #F (comprehension_functor_cod_mor χ₁ xx).
Proof.
  refine (pr2 (Fχ x xx) @ _).
  apply id_right.
Qed.

Proposition comprehension_nat_trans_comm
            {C₁ C₂ : cat_with_terminal_cleaving}
            {χ₁ : comprehension_functor C₁}
            {χ₂ : comprehension_functor C₂}
            {F : functor_with_terminal_cleaving C₁ C₂}
            (Fχ : comprehension_nat_trans χ₁ χ₂ F)
            {x y : C₁}
            {f : x --> y}
            {xx : disp_cat_of_types C₁ x}
            {yy : disp_cat_of_types C₁ y}
            (ff : xx -->[ f ] yy)
  : #F (comprehension_functor_mor χ₁ ff)
    · comprehension_nat_trans_mor Fχ yy
    =
    comprehension_nat_trans_mor Fχ xx
    · comprehension_functor_mor χ₂ (♯ (comp_cat_type_functor F) ff).
Proof.
  refine (maponpaths pr1 (pr2 Fχ x y f xx yy ff) @ _).
  unfold transportb.
  refine (pr1_transportf (A := C₂⟦_,_⟧) _ _ @ _).
  rewrite transportf_const ; cbn.
  apply idpath.
Qed.

Definition id_comprehension_nat_trans
           {C : cat_with_terminal_cleaving}
           (χ : comprehension_functor C)
  : comprehension_nat_trans χ χ (id₁ _).
Proof.
  simple refine (_ ,, _).
  - refine (λ x xx, identity _ ,, _).
    abstract
      (cbn ;
       rewrite id_left, id_right ;
       apply idpath).
  - abstract
      (intros x₁ x₂ f xx₁ xx₂ ff ;
       use subtypePath ; [ intro ; apply homset_property | ] ;
       unfold transportb ;
       refine (!_) ;
       refine (pr1_transportf (A := C⟦_,_⟧) _ _ @ _) ;
       rewrite transportf_const ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition comp_comprehension_nat_trans
           {C₁ C₂ C₃ : cat_with_terminal_cleaving}
           {χ₁ : comprehension_functor C₁}
           {χ₂ : comprehension_functor C₂}
           {χ₃ : comprehension_functor C₃}
           {F : functor_with_terminal_cleaving C₁ C₂}
           {G : functor_with_terminal_cleaving C₂ C₃}
           (Fχ : comprehension_nat_trans χ₁ χ₂ F)
           (Gχ : comprehension_nat_trans χ₂ χ₃ G)
  : comprehension_nat_trans χ₁ χ₃ (F · G).
Proof.
  simple refine (_ ,, _).
  - refine (λ x xx,
            #G (comprehension_nat_trans_mor Fχ xx) · comprehension_nat_trans_mor Gχ _
            ,,
            _).
    abstract
      (cbn ;
       rewrite id_right ;
       rewrite !assoc' ;
       etrans ;
       [ apply maponpaths ;
         apply comprehension_nat_trans_mor_comm
       | ] ;
       rewrite <- functor_comp ;
       apply maponpaths ;
       apply comprehension_nat_trans_mor_comm).
  - abstract
      (intros x₁ x₂ f xx₁ xx₂ ff ;
       use subtypePath ; [ intro ; apply homset_property | ] ;
       unfold transportb ;
       refine (!_) ;
       refine (pr1_transportf (A := C₃⟦_,_⟧) _ _ @ _) ;
       rewrite transportf_const ; cbn ;
       rewrite !assoc ;
       rewrite <- functor_comp ;
       refine (!_) ;
       etrans ;
       [ apply maponpaths_2 ;
         apply maponpaths ;
         exact (comprehension_nat_trans_comm Fχ ff)
       | ] ;
       rewrite functor_comp ;
       rewrite !assoc' ;
       apply maponpaths ;
       apply (comprehension_nat_trans_comm Gχ)).
Defined.

Definition comprehension_nat_trans_eq
           {C₁ C₂ : cat_with_terminal_cleaving}
           {F G : functor_with_terminal_cleaving C₁ C₂}
           (τ : nat_trans_with_terminal_cleaving F G)
           {χ₁ : comprehension_functor C₁}
           {χ₂ : comprehension_functor C₂}
           (Fχ : comprehension_nat_trans χ₁ χ₂ F)
           (Gχ : comprehension_nat_trans χ₁ χ₂ G)
  : UU
  := ∏ (x : C₁)
       (xx : disp_cat_of_types C₁ x),
     comprehension_nat_trans_mor Fχ xx
     · comprehension_functor_mor χ₂ (comp_cat_type_nat_trans τ x xx)
     =
     τ _ · comprehension_nat_trans_mor Gχ xx.

Proposition isaprop_comprehension_nat_trans_eq
            {C₁ C₂ : cat_with_terminal_cleaving}
            {F G : functor_with_terminal_cleaving C₁ C₂}
            (τ : nat_trans_with_terminal_cleaving F G)
            {χ₁ : comprehension_functor C₁}
            {χ₂ : comprehension_functor C₂}
            (Fχ : comprehension_nat_trans χ₁ χ₂ F)
            (Gχ : comprehension_nat_trans χ₁ χ₂ G)
  : isaprop (comprehension_nat_trans_eq τ Fχ Gχ).
Proof.
  do 2 (use impred ; intro).
  apply homset_property.
Qed.

Definition disp_cat_ob_mor_cat_terminal_cleaving_functor
  : disp_cat_ob_mor bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact comprehension_functor.
  - exact (λ C₁ C₂ χ₁ χ₂ F, comprehension_nat_trans χ₁ χ₂ F).
Defined.

Definition disp_cat_id_comp_cat_terminal_cleaving_functor
  : disp_cat_id_comp
      bicat_cat_with_terminal_cleaving
      disp_cat_ob_mor_cat_terminal_cleaving_functor.
Proof.
  simple refine (_ ,, _).
  - exact (λ C χ, id_comprehension_nat_trans χ).
  - exact (λ C₁ C₂ C₃ F G χ₁ χ₂ χ₃ Fχ Gχ, comp_comprehension_nat_trans Fχ Gχ).
Defined.

Definition disp_cat_data_cat_terminal_cleaving_functor
  : disp_cat_data bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_cat_terminal_cleaving_functor.
  - exact disp_cat_id_comp_cat_terminal_cleaving_functor.
Defined.

Definition disp_prebicat_1_id_comp_cells_cat_terminal_cleaving_functor
  : disp_prebicat_1_id_comp_cells bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_cat_terminal_cleaving_functor.
  - exact (λ C₁ C₂ F G τ χ₁ χ₂ Fχ Gχ, comprehension_nat_trans_eq τ Fχ Gχ).
Defined.

Proposition disp_prebicat_ops_cat_terminal_cleaving_functor
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_cat_terminal_cleaving_functor.
Proof.
  repeat split.
  - intros C₁ C₂ F χ₁ χ₂ Fχ x xx ; cbn.
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    apply id_right.
  - intros C₁ C₂ F χ₁ χ₂ Fχ x xx ; cbn.
    rewrite functor_id.
    rewrite !id_left.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    apply id_right.
  - intros C₁ C₂ F χ₁ χ₂ Fχ x xx ; cbn.
    rewrite id_left, id_right.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    apply id_right.
  - intros C₁ C₂ F χ₁ χ₂ Fχ x xx ; cbn.
    rewrite functor_id.
    rewrite !id_left.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    apply id_right.
  - intros C₁ C₂ F χ₁ χ₂ Fχ x xx ; cbn.
    rewrite id_left, id_right.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    apply id_right.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ χ₁ χ₂ χ₃ χ₄ Fχ₁ Fχ₂ Fχ₃ x xx ; cbn.
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    rewrite id_right.
    rewrite functor_comp.
    rewrite !assoc'.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ χ₁ χ₂ χ₃ χ₄ Fχ₁ Fχ₂ Fχ₃ x xx ; cbn.
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    rewrite id_right.
    rewrite functor_comp.
    rewrite !assoc'.
    apply idpath.
  - intros C₁ C₂ F₁ F₂ F₃ τ₁ τ₂ χ₁ χ₂ χ₃ Fχ₁ Fχ₂ p q x xx ; cbn ; cbn in p, q.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_comp.

    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply p.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply q.
    }
    apply idpath.
  - intros C₁ C₂ C₃ F G₁ G₂ τ χ₁ χ₂ χ₃ Fχ Gχ₁ Gχ₂ p x xx ; cbn ; cbn in p.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply p.
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply nat_trans_ax.
  - intros C₁ C₂ C₃ F₁ F₂ G τ χ₁ χ₂ χ₃ Fχ₁ Fχ₂ Gχ p x xx ; cbn ; cbn in p.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comprehension_nat_trans_comm.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !functor_comp.
    apply maponpaths.
    apply p.
Qed.

 Definition disp_prebicat_data_cat_terminal_cleaving_functor
  : disp_prebicat_data bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_cat_terminal_cleaving_functor.
  - exact disp_prebicat_ops_cat_terminal_cleaving_functor.
Defined.

Proposition disp_prebicat_laws_cat_terminal_cleaving_functor
  : disp_prebicat_laws disp_prebicat_data_cat_terminal_cleaving_functor.
Proof.
  repeat split ; intro ; intros ; apply isaprop_comprehension_nat_trans_eq.
Qed.

Definition disp_prebicat_cat_terminal_cleaving_functor
  : disp_prebicat bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_cat_terminal_cleaving_functor.
  - exact disp_prebicat_laws_cat_terminal_cleaving_functor.
Defined.

Definition disp_bicat_cat_terminal_cleaving_functor
  : disp_bicat bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_cat_terminal_cleaving_functor.
  - abstract
      (intro ; intros ;
       apply isasetaprop ;
       apply isaprop_comprehension_nat_trans_eq).
Defined.

Proposition disp_2cells_isaprop_disp_bicat_cat_terminal_cleaving_functor
  : disp_2cells_isaprop disp_bicat_cat_terminal_cleaving_functor.
Proof.
  intro ; intros.
  apply isaprop_comprehension_nat_trans_eq.
Qed.

Proposition disp_locally_groupoid_disp_bicat_cat_terminal_cleaving_functor
  : disp_locally_groupoid disp_bicat_cat_terminal_cleaving_functor.
Proof.
  use make_disp_locally_groupoid_univalent_2_1.
  - refine (λ (C₁ C₂ : cat_with_terminal_cleaving)
              (F : functor_with_terminal_cleaving C₁ C₂)
              (χ₁ : comprehension_functor C₁)
              (χ₂ : comprehension_functor C₂)
              (Fχ₁ Fχ₂ : comprehension_nat_trans χ₁ χ₂ F)
              (p : comprehension_nat_trans_eq (id₂ _) Fχ₁ Fχ₂), _).
    simple refine (_ ,, _ ,, _) ;
    try (apply disp_2cells_isaprop_disp_bicat_cat_terminal_cleaving_functor).
    intros x xx ; cbn.
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    rewrite id_right.
    pose (q := p x xx).
    cbn in q.
    rewrite id_left in q.
    refine (!q @ _).
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_id.
    }
    apply id_right.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
Qed.

Proposition disp_univalent_2_1_disp_bicat_cat_terminal_cleaving_functor
  : disp_univalent_2_1 disp_bicat_cat_terminal_cleaving_functor.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  refine (λ (C₁ C₂ : cat_with_terminal_cleaving)
            (F : functor_with_terminal_cleaving C₁ C₂)
            (χ₁ : comprehension_functor C₁)
            (χ₂ : comprehension_functor C₂)
            (Fχ₁ Fχ₂ : comprehension_nat_trans χ₁ χ₂ F),
          _).
  use isweqimplimpl.
  - intros p ; cbn.
    use disp_nat_trans_eq.
    intros x xx.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    refine (_ @ pr1 p x xx @ _) ; cbn.
    + refine (!_).
      refine (_ @ id_right _).
      apply maponpaths.
      apply comprehension_functor_mor_id.
    + apply id_left.
  - cbn -[isaprop].
    unfold comprehension_nat_trans in *.
    use (isaset_disp_nat_trans
             _
             (disp_functor_composite χ₁ (disp_codomain_functor F))
             (disp_functor_composite (comp_cat_type_functor F) χ₂)).
  - use isaproptotal2.
    + intro.
      apply isaprop_is_disp_invertible_2cell.
    + intros.
      apply isaprop_comprehension_nat_trans_eq.
Qed.

Section AdjEquivs.
  Context {C : cat_with_terminal_cleaving}
          (χ₁ χ₂ : comprehension_functor C).

  Section ToAdjEquiv.
    Context (τ : disp_nat_z_iso χ₁ χ₂ (nat_z_iso_id (functor_identity C))).

    Definition disp_nat_z_iso_adjequiv_map
      : comprehension_nat_trans χ₁ χ₂ (id₁ C).
    Proof.
      simple refine (_ ,, _).
      - exact (λ x xx, τ x xx).
      - abstract
          (intros x y f xx yy ff ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           rewrite transportb_cod_disp ; cbn ;
           pose (p := maponpaths pr1 (disp_nat_trans_ax τ ff)) ;
           rewrite transportb_cod_disp in p ;
           exact p).
    Defined.

    Let θ : disp_nat_z_iso χ₂ χ₁ _
      := disp_nat_z_iso_inv τ.

    Definition disp_nat_z_iso_adjequiv_inv
      : comprehension_nat_trans χ₂ χ₁ (id₁ C).
    Proof.
      simple refine (_ ,, _).
      - exact (λ x xx, θ x xx).
      - abstract
          (intros x y f xx yy ff ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           rewrite transportb_cod_disp ; cbn ;
           pose (p := maponpaths pr1 (disp_nat_trans_ax θ ff)) ;
           rewrite transportb_cod_disp in p ;
           exact p).
    Defined.
  End ToAdjEquiv.

  Definition disp_nat_z_iso_to_adjequiv
             (τ : disp_nat_z_iso χ₁ χ₂ (nat_z_iso_id (functor_identity C)))
    : disp_adjoint_equivalence
        (D := disp_bicat_cat_terminal_cleaving_functor)
        (internal_adjoint_equivalence_identity C)
        χ₁ χ₂.
  Proof.
    simple refine (_ ,, ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _)))).
    - exact (disp_nat_z_iso_adjequiv_map τ).
    - exact (disp_nat_z_iso_adjequiv_inv τ).
    - abstract
        (intros x xx ; cbn ;
         unfold comprehension_nat_trans_mor ; cbn ;
         rewrite !id_left ;
         refine (comprehension_functor_mor_id _ _ @ _) ;
         refine (!_) ;
         refine (maponpaths pr1 (disp_nat_z_iso_iso_inv τ x xx) @ _) ;
         rewrite transportb_cod_disp ;
         apply idpath).
    - abstract
        (intros x xx ; cbn ;
         unfold comprehension_nat_trans_mor ; cbn ;
         rewrite !id_left ;
         refine (maponpaths (λ z, _ · z) (comprehension_functor_mor_id _ _) @ _) ;
         rewrite id_right ;
         refine (maponpaths pr1 (disp_nat_z_iso_inv_iso τ x xx) @ _) ;
         rewrite transportb_cod_disp ;
         apply idpath).
    - apply disp_2cells_isaprop_disp_bicat_cat_terminal_cleaving_functor.
    - apply disp_2cells_isaprop_disp_bicat_cat_terminal_cleaving_functor.
    - apply disp_locally_groupoid_disp_bicat_cat_terminal_cleaving_functor.
    - apply disp_locally_groupoid_disp_bicat_cat_terminal_cleaving_functor.
  Defined.

  Definition adjequiv_to_disp_nat_z_iso
             (τ : disp_adjoint_equivalence
                    (D := disp_bicat_cat_terminal_cleaving_functor)
                    (internal_adjoint_equivalence_identity C)
                    χ₁ χ₂)
    : disp_nat_z_iso χ₁ χ₂ (nat_z_iso_id (functor_identity C)).
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact (λ x xx, pr11 τ x xx).
    - abstract
        (intros x y f xx yy ff ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         rewrite transportb_cod_disp ; cbn ;
         pose (p := maponpaths pr1 (disp_nat_trans_ax (pr1 τ) ff)) ;
         rewrite transportb_cod_disp in p ;
         exact p).
    - intros x xx ; cbn.
      simple refine (_ ,, (_ ,, _)).
      + exact (pr1 (pr112 τ) x xx).
      + abstract
          (use subtypePath ; [ intro ; apply homset_property | ] ;
           rewrite transportb_cod_disp ; cbn ;
           pose (p := pr2 (pr212 τ) x xx) ; cbn in p ;
           rewrite !id_left in p ;
           refine (_ @ p) ;
           refine (!(id_right _) @ _) ;
           apply maponpaths ;
           refine (!_) ;
           apply comprehension_functor_mor_id).
      + abstract
          (use subtypePath ; [ intro ; apply homset_property | ] ;
           rewrite transportb_cod_disp ; cbn ;
           pose (p := pr1 (pr212 τ) x xx) ; cbn in p ;
           rewrite !id_left in p ;
           refine (!p @ _) ;
           apply comprehension_functor_mor_id).
  Defined.

  Definition disp_nat_z_iso_weq_disp_adjequiv
    : disp_nat_z_iso χ₁ χ₂ (nat_z_iso_id (functor_identity C))
      ≃
      disp_adjoint_equivalence
        (D := disp_bicat_cat_terminal_cleaving_functor)
        (internal_adjoint_equivalence_identity C)
        χ₁ χ₂.
  Proof.
    use weq_iso.
    - exact disp_nat_z_iso_to_adjequiv.
    - exact adjequiv_to_disp_nat_z_iso.
    - abstract
        (intros τ ;
         use subtypePath ; [ intro ; apply isaprop_is_disp_nat_z_iso | ] ;
         use disp_nat_trans_eq ;
         intros x xx ;
         apply idpath).
    - abstract
        (intros τ ;
         use subtypePath ;
         [ intro ;
           use (isaprop_disp_left_adjoint_equivalence
                  _ _
                  is_univalent_2_1_bicat_cat_with_terminal_cleaving) ;
           exact disp_univalent_2_1_disp_bicat_cat_terminal_cleaving_functor
         | ] ;
         use disp_nat_trans_eq ;
         intros x xx ;
         apply idpath).
  Defined.
End AdjEquivs.

Proposition fiberwise_univalent_2_0_disp_bicat_cat_terminal_cleaving_functor
  : fiberwise_univalent_2_0 disp_bicat_cat_terminal_cleaving_functor.
Proof.
  refine (λ (C : cat_with_terminal_cleaving) (χ₁ χ₂ : comprehension_functor C), _).
  use weqhomot.
  - exact (disp_nat_z_iso_weq_disp_adjequiv χ₁ χ₂
           ∘ disp_functor_eq_weq χ₁ χ₂ (disp_univalent_disp_codomain C))%weq.
  - intro p ; cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      use (isaprop_disp_left_adjoint_equivalence
             _ _
             is_univalent_2_1_bicat_cat_with_terminal_cleaving).
      exact disp_univalent_2_1_disp_bicat_cat_terminal_cleaving_functor.
    }
    use disp_nat_trans_eq.
    intros x xx.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    apply idpath.
Qed.

Proposition disp_univalent_2_0_disp_bicat_cat_terminal_cleaving_functor
  : disp_univalent_2_0 disp_bicat_cat_terminal_cleaving_functor.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  exact fiberwise_univalent_2_0_disp_bicat_cat_terminal_cleaving_functor.
Qed.

Definition bicat_cat_terminal_cleaving_functor
  : bicat
  := total_bicat disp_bicat_cat_terminal_cleaving_functor.

Proposition is_univalent_2_1_bicat_cat_terminal_cleaving_functor
  : is_univalent_2_1 bicat_cat_terminal_cleaving_functor.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_1_disp_bicat_cat_terminal_cleaving_functor.
Qed.

Proposition is_univalent_2_0_bicat_cat_terminal_cleaving_functor
  : is_univalent_2_0 bicat_cat_terminal_cleaving_functor.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_0_disp_bicat_cat_terminal_cleaving_functor.
Qed.

Proposition is_univalent_2_bicat_cat_terminal_cleaving_functor
  : is_univalent_2 bicat_cat_terminal_cleaving_functor.
Proof.
  split.
  - exact is_univalent_2_0_bicat_cat_terminal_cleaving_functor.
  - exact is_univalent_2_1_bicat_cat_terminal_cleaving_functor.
Qed.

Definition cat_with_terminal_cleaving_functor
  : UU
  := bicat_cat_terminal_cleaving_functor.

Definition make_cat_with_terminal_cleaving_functor
           (C : bicat_cat_with_terminal_cleaving)
           (χ : comprehension_functor C)
  : cat_with_terminal_cleaving_functor
  := C ,, χ.

Coercion cat_terminal_cleaving_functor_to_cat_terminal_cleaving
         (C : cat_with_terminal_cleaving_functor)
  : cat_with_terminal_cleaving
  := pr1 C.

Definition comp_cat_comprehension
           (C : cat_with_terminal_cleaving_functor)
  : comprehension_functor C
  := pr2 C.

Definition functor_with_terminal_cleaving_functor
           (C₁ C₂ : cat_with_terminal_cleaving_functor)
  : UU
  := C₁ --> C₂.

Definition make_functor_with_terminal_cleaving_functor
           {C₁ C₂ : cat_with_terminal_cleaving_functor}
           (F : functor_with_terminal_cleaving C₁ C₂)
           (Fχ : comprehension_nat_trans
                   (comp_cat_comprehension C₁)
                   (comp_cat_comprehension C₂)
                   F)
  : functor_with_terminal_cleaving_functor C₁ C₂
  := F ,, Fχ.

Coercion functor_with_terminal_cleaving_functor_to_functor_with_terminal_cleaving
         {C₁ C₂ : cat_with_terminal_cleaving_functor}
         (F : functor_with_terminal_cleaving_functor C₁ C₂)
  : functor_with_terminal_cleaving C₁ C₂
  := pr1 F.

Definition comp_cat_functor_comprehension
           {C₁ C₂ : cat_with_terminal_cleaving_functor}
           (F : functor_with_terminal_cleaving_functor C₁ C₂)
  : comprehension_nat_trans
      (comp_cat_comprehension C₁)
      (comp_cat_comprehension C₂)
      F
  := pr2 F.

Definition nat_trans_with_terminal_cleaving_functor
           {C₁ C₂ : cat_with_terminal_cleaving_functor}
           (F G : functor_with_terminal_cleaving_functor C₁ C₂)
  : UU
  := F ==> G.

Definition make_nat_trans_with_terminal_cleaving_functor
           {C₁ C₂ : cat_with_terminal_cleaving_functor}
           {F G : functor_with_terminal_cleaving_functor C₁ C₂}
           (τ : nat_trans_with_terminal_cleaving F G)
           (Hτ : comprehension_nat_trans_eq
                   τ
                   (comp_cat_functor_comprehension F)
                   (comp_cat_functor_comprehension G))
  : nat_trans_with_terminal_cleaving_functor F G
  := τ ,, Hτ.

Coercion nat_trans_with_terminal_cleaving_functor_to_nat_trans_with_terminal_cleaving
         {C₁ C₂ : cat_with_terminal_cleaving_functor}
         {F G : functor_with_terminal_cleaving_functor C₁ C₂}
         (τ : nat_trans_with_terminal_cleaving_functor F G)
  : nat_trans_with_terminal_cleaving F G
  := pr1 τ.

Definition comp_cat_nat_trans_comprehension
           {C₁ C₂ : cat_with_terminal_cleaving_functor}
           {F G : functor_with_terminal_cleaving_functor C₁ C₂}
           (τ : nat_trans_with_terminal_cleaving_functor F G)
           {x : C₁}
           (xx : disp_cat_of_types C₁ x)
  : comprehension_nat_trans_mor
      (comp_cat_functor_comprehension F)
      xx
    · comprehension_functor_mor
        (comp_cat_comprehension C₂)
        (comp_cat_type_nat_trans τ x xx)
    =
    τ _ · comprehension_nat_trans_mor (comp_cat_functor_comprehension G) xx
  := pr2 τ x xx.

(** * 4. Bicategory of full comprehension categories *)
Definition is_full_comp_cat
           (C : cat_with_terminal_cleaving_functor)
  : UU
  := is_cartesian_disp_functor (comp_cat_comprehension C)
     ×
     disp_functor_ff (comp_cat_comprehension C).

Proposition isaprop_is_full_comp_cat
            (C : cat_with_terminal_cleaving_functor)
  : isaprop (is_full_comp_cat C).
Proof.
  use isapropdirprod.
  - apply isaprop_is_cartesian_disp_functor.
  - apply isaprop_disp_functor_ff.
Qed.

Definition disp_bicat_full_comp_cat
  : disp_bicat bicat_cat_terminal_cleaving_functor.
Proof.
  use disp_subbicat.
  - exact is_full_comp_cat.
  - exact (λ (C₁ C₂ : cat_with_terminal_cleaving_functor)
             (P₁ : is_full_comp_cat C₁)
             (P₂ : is_full_comp_cat C₂)
             (F : functor_with_terminal_cleaving_functor C₁ C₂),
            ∏ (x : C₁)
              (xx : disp_cat_of_types C₁ x),
            is_z_isomorphism
              (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) xx)).
  - intros C P x xx.
    apply identity_is_z_iso.
  - intros C₁ C₂ C₃ P₁ P₂ P₃ F G H₁ H₂ x xx.
    cbn.
    use is_z_iso_comp_of_is_z_isos.
    + apply (functor_on_z_iso _ (_ ,, H₁ x xx)).
    + apply H₂.
Defined.

Proposition disp_univalent_2_1_disp_bicat_full_comp_cat
  : disp_univalent_2_1 disp_bicat_full_comp_cat.
Proof.
  apply disp_subbicat_univalent_2_1.
  intro ; intros.
  do 2 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

Proposition disp_univalent_2_0_disp_bicat_full_comp_cat
  : disp_univalent_2_0 disp_bicat_full_comp_cat.
Proof.
  use disp_subbicat_univalent_2_0.
  - exact is_univalent_2_bicat_cat_terminal_cleaving_functor.
  - intro.
    apply isaprop_is_full_comp_cat.
  - intros.
    do 2 (use impred ; intro).
    apply isaprop_is_z_isomorphism.
Qed.

Definition bicat_full_comp_cat
  : bicat
  := total_bicat disp_bicat_full_comp_cat.

Proposition is_univalent_2_1_bicat_full_comp_cat
  : is_univalent_2_1 bicat_full_comp_cat.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_cat_terminal_cleaving_functor.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Proposition is_univalent_2_0_bicat_full_comp_cat
  : is_univalent_2_0 bicat_full_comp_cat.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_cat_terminal_cleaving_functor.
  - exact disp_univalent_2_0_disp_bicat_full_comp_cat.
Qed.

Proposition is_univalent_2_bicat_full_comp_cat
  : is_univalent_2 bicat_full_comp_cat.
Proof.
  split.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - exact is_univalent_2_1_bicat_full_comp_cat.
Qed.

Definition full_comp_cat
  : UU
  := bicat_full_comp_cat.

Definition make_full_comp_cat
           (C : cat_with_terminal_cleaving_functor)
           (H₁ : is_cartesian_disp_functor (comp_cat_comprehension C))
           (H₂ : disp_functor_ff (comp_cat_comprehension C))
  : full_comp_cat
  := C ,, (H₁ ,, H₂) ,, tt.

Coercion full_comp_cat_to_cat_with_terminal_cleaving
         (C : full_comp_cat)
  : cat_with_terminal_cleaving_functor
  := pr1 C.

Definition full_comp_cat_comprehension_cartesian
           (C : full_comp_cat)
  : is_cartesian_disp_functor (comp_cat_comprehension C)
  := pr112 C.

Definition full_comp_cat_comprehension_fully_faithful
           (C : full_comp_cat)
  : disp_functor_ff (comp_cat_comprehension C)
  := pr212 C.

Definition full_comp_cat_functor
           (C₁ C₂ : full_comp_cat)
  : UU
  := C₁ --> C₂.

Definition make_full_comp_cat_functor
           {C₁ C₂ : full_comp_cat}
           (F : functor_with_terminal_cleaving_functor C₁ C₂)
           (HF : ∏ (x : C₁)
                   (xx : disp_cat_of_types C₁ x),
                 is_z_isomorphism
                   (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) xx))
  : full_comp_cat_functor C₁ C₂
  := F ,, tt ,, HF.

Coercion full_comp_cat_functor_to_functor_with_terminal_cleaving_functor
         {C₁ C₂ : full_comp_cat}
         (F : full_comp_cat_functor C₁ C₂)
  : functor_with_terminal_cleaving_functor C₁ C₂
  := pr1 F.

Definition full_comp_cat_functor_is_z_iso
           {C₁ C₂ : full_comp_cat}
           (F : full_comp_cat_functor C₁ C₂)
           {x : C₁}
           (xx : disp_cat_of_types C₁ x)
  : is_z_isomorphism
      (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) xx)
  := pr22 F x xx.

Definition full_comp_cat_nat_trans
           {C₁ C₂ : full_comp_cat}
           (F G : full_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion full_comp_cat_nat_trans_to_nat_trans_with_terminal_cleaving_functor
         {C₁ C₂ : full_comp_cat}
         {F G : full_comp_cat_functor C₁ C₂}
         (τ : full_comp_cat_nat_trans F G)
  : nat_trans_with_terminal_cleaving_functor F G
  := pr1 τ.

Definition make_full_comp_cat_nat_trans
           {C₁ C₂ : full_comp_cat}
           {F G : full_comp_cat_functor C₁ C₂}
           (τ : nat_trans_with_terminal_cleaving_functor F G)
  : full_comp_cat_nat_trans F G
  := τ ,, tt ,, tt.

Proposition full_comp_nat_trans_eq
            {C₁ C₂ : full_comp_cat}
            {F G : full_comp_cat_functor C₁ C₂}
            {τ₁ τ₂ : full_comp_cat_nat_trans F G}
            (p : ∏ (x : C₁), τ₁ x = τ₂ x)
            (p' := nat_trans_eq (homset_property _) _ _ _ _ p)
            (pp : ∏ (x : C₁)
                    (xx : disp_cat_of_types C₁ x),
                  transportf
                    _
                    (nat_trans_eq_pointwise p' x)
                    (comp_cat_type_nat_trans τ₁ x xx)
                  =
                  comp_cat_type_nat_trans τ₂ x xx)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    use isapropdirprod ; apply isapropunit.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_comprehension_nat_trans_eq.
  }
  use subtypePath.
  {
    intro.
    use isapropdirprod ; apply isapropunit.
  }
  use total2_paths_f.
  - use nat_trans_eq.
    {
      apply homset_property.
    }
    exact p.
  - etrans.
    {
      use transportf_dirprod.
    }
    use dirprodeq.
    + simpl.
      rewrite transportf_const.
      apply (proofirrelevance _ (isapropdirprod _ _ isapropunit isapropunit)).
    + simpl.
      use disp_nat_trans_eq.
      intros x xx.
      etrans.
      {
        use disp_nat_trans_transportf.
      }
      apply pp.
Qed.
