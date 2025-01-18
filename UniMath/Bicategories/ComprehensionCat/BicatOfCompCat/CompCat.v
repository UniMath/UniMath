(*******************************************************************************************

 The bicategory of comprehension categories

 Our goal is to construct the bicategory of full comprehension categories, and to do so, we
 use displayed bicategories. Starting with the bicategory of univalent categories, we add the
 following structure to it in the following order.
 1. A displayed category and a terminal object.
 2. A cleaving for the displayed category.
 3. A comprehension functor.
 4. A proof that this comprehension functor is fully faithful.
 In this file, we look at the third of these.

 This is the most involved step of these, because we do it by hand. More specifically, we
 first define the notion of comprehension functor ([comprehension_functor]) and
 transformation ([comprehension_nat_trans]), and with those, we construct the displayed
 bicategory of comprehension categories ([disp_bicat_comp_cat]). Most work lies in showing
 that this bicategory is univalent. To do so, we reuse the fact that equality of displayed
 functors is given by displayed natural isomorphisms.

 Up to now, we have put the following data and properties together:
 - A univalent category `C`.
 - A univalent displayed category `D`.
 - A terminal object `T` in `C`.
 - A cleaving `HD` for `D`.
 - A comprehension functor for `D` (which is a cartesian displayed functor from `D` to the
   codomain displayed category).

 It is worth commenting on the morphisms in the bicategory of comprehension categories that
 we define in this file ([bicat_comp_cat]). The morphism in this bicategory, are lax rather
 than pseudo. More specifically, let us say that we have two comprehension categories `C₁`
 and `C₂` whose comprehension functors are given by `χ₁ : D₁ ⟶ Arr(C₁)` and
 `χ₂ : D₂ ⟶ Arr(C₂)` respectively. If we have a morphism between them, then we have functors
 `FF : D₁ ⟶ D₂` and `Arr(F) : Arr(C₁) ⟶ Arr(C₂)` (where `F` is the functor between the
 base categories of `C₁` and `C₂`). Now we have two functors  `D₁ ⟶ Arr(C₂)`, namely
 `χ₁ · Arr(F)` and `FF · χ₂`. We have multiple options available to express the commutativity
 of this diagram.
 1. We could require there to be a natural transformation from `χ₁ · Arr(F)` to `FF · χ₂`.
    This is called a lax morphism (Definition 3.3.1.3 in 'Categorical structures for deduction').
 2. We could require there to be a natural transformation in the opposite direction, and this
    is called an oplax morphism.
 3. We could require there to be a natural isomorphism, and this is called a pseudo morphism.
 In this file, we use the first option of these.

 Finally, we compare our definition of comprehension category to the one already present in
 UniMath in the file `DisplayedCats.ComprehensionC` (Definition 6.1 in 'Displayed Categories'
 by Ahrens and Lumsdaine). While they are mostly similar, there are a couple of slight
 differences between the two definitions:
 - In this file, the involved categories are required to be univalent, which is not required
   in the definition by Ahrens and Lumsdaine.
 - We require there to be a terminal object in `C`, which is not required by Ahrens and
   Lumsdaine.

 References:
 - 'Displayed Categories' by Ahrens and Lumsdaine (https://lmcs.episciences.org/5252/pdf).
 - 'Categorical structures for deduction' by Coraglia (https://etagreta.github.io/docs/coraglia_phdthesis-oneside2023.pdf)
 - 'Categorical Logic and Type Theory' by Jacobs

 Contents
 1. Comprehension functors
 2. Comprehension natural transformations
 3. The displayed bicategory of comprehension categories
 4. The univalence of this displayed bicategory
 5. Builders and accessors
 6. Comparison
 7. Adjoint equivalences

 *******************************************************************************************)
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
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.DispCatTerminal.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FibTerminal.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.

(** * 1. Comprehension functors *)
Definition comprehension_functor
           (C : cat_with_terminal_cleaving)
  : UU
  := cartesian_disp_functor
       (functor_identity C)
       (disp_cat_of_types C)
       (disp_codomain C).

Definition make_comprehension_functor
           {C : cat_with_terminal_cleaving}
           (FF : disp_functor
                   (functor_identity C)
                   (disp_cat_of_types C)
                   (disp_codomain C))
           (HFF : is_cartesian_disp_functor FF)
  : comprehension_functor C
  := FF ,, HFF.

Identity Coercion comprehension_functor_to_cartesian_disp_functor
  : comprehension_functor >-> cartesian_disp_functor.

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

Proposition comprehension_functor_mor_transportf
            {C : cat_with_terminal_cleaving}
            (χ : comprehension_functor C)
            {x y : C}
            {f g : x --> y}
            (p : f = g)
            {xx : disp_cat_of_types C x}
            {yy : disp_cat_of_types C y}
            (ff : xx -->[ f ] yy)
  : comprehension_functor_mor χ (transportf _ p ff)
    =
    comprehension_functor_mor χ ff.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition comprehension_functor_mor_transportb
            {C : cat_with_terminal_cleaving}
            (χ : comprehension_functor C)
            {x y : C}
            {f g : x --> y}
            (p : f = g)
            {xx : disp_cat_of_types C x}
            {yy : disp_cat_of_types C y}
            (gg : xx -->[ g ] yy)
  : comprehension_functor_mor χ (transportb _ p gg)
    =
    comprehension_functor_mor χ gg.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

(** * 2. Comprehension natural transformations *)
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

(** * 3. The displayed bicategory of comprehension categories *)
Definition disp_cat_ob_mor_comp_cat
  : disp_cat_ob_mor bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact comprehension_functor.
  - exact (λ C₁ C₂ χ₁ χ₂ F, comprehension_nat_trans χ₁ χ₂ F).
Defined.

Definition disp_cat_id_comp_comp_cat
  : disp_cat_id_comp
      bicat_cat_with_terminal_cleaving
      disp_cat_ob_mor_comp_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ C χ, id_comprehension_nat_trans χ).
  - exact (λ C₁ C₂ C₃ F G χ₁ χ₂ χ₃ Fχ Gχ, comp_comprehension_nat_trans Fχ Gχ).
Defined.

Definition disp_cat_data_comp_cat
  : disp_cat_data bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_comp_cat.
  - exact disp_cat_id_comp_comp_cat.
Defined.

Definition disp_prebicat_1_id_comp_cells_comp_cat
  : disp_prebicat_1_id_comp_cells bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_comp_cat.
  - exact (λ C₁ C₂ F G τ χ₁ χ₂ Fχ Gχ, comprehension_nat_trans_eq τ Fχ Gχ).
Defined.

Proposition disp_prebicat_ops_comp_cat
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_comp_cat.
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

Definition disp_prebicat_data_comp_cat
  : disp_prebicat_data bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_comp_cat.
  - exact disp_prebicat_ops_comp_cat.
Defined.

Proposition disp_prebicat_laws_comp_cat
  : disp_prebicat_laws disp_prebicat_data_comp_cat.
Proof.
  repeat split ; intro ; intros ; apply isaprop_comprehension_nat_trans_eq.
Qed.

Definition disp_prebicat_comp_cat
  : disp_prebicat bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_comp_cat.
  - exact disp_prebicat_laws_comp_cat.
Defined.

Definition disp_bicat_comp_cat
  : disp_bicat bicat_cat_with_terminal_cleaving.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_comp_cat.
  - abstract
      (intro ; intros ;
       apply isasetaprop ;
       apply isaprop_comprehension_nat_trans_eq).
Defined.

Definition bicat_comp_cat
  : bicat
  := total_bicat disp_bicat_comp_cat.

Proposition disp_2cells_isaprop_disp_bicat_comp_cat
  : disp_2cells_isaprop disp_bicat_comp_cat.
Proof.
  intro ; intros.
  apply isaprop_comprehension_nat_trans_eq.
Qed.

Proposition disp_locally_groupoid_disp_bicat_comp_cat
  : disp_locally_groupoid disp_bicat_comp_cat.
Proof.
  use make_disp_locally_groupoid_univalent_2_1.
  - refine (λ (C₁ C₂ : cat_with_terminal_cleaving)
              (F : functor_with_terminal_cleaving C₁ C₂)
              (χ₁ : comprehension_functor C₁)
              (χ₂ : comprehension_functor C₂)
              (Fχ₁ Fχ₂ : comprehension_nat_trans χ₁ χ₂ F)
              (p : comprehension_nat_trans_eq (id₂ _) Fχ₁ Fχ₂), _).
    simple refine (_ ,, _ ,, _) ;
    try (apply disp_2cells_isaprop_disp_bicat_comp_cat).
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

(** * 4. The univalence of this displayed bicategory *)
Proposition disp_univalent_2_1_disp_bicat_comp_cat
  : disp_univalent_2_1 disp_bicat_comp_cat.
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
        (D := disp_bicat_comp_cat)
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
    - apply disp_2cells_isaprop_disp_bicat_comp_cat.
    - apply disp_2cells_isaprop_disp_bicat_comp_cat.
    - apply disp_locally_groupoid_disp_bicat_comp_cat.
    - apply disp_locally_groupoid_disp_bicat_comp_cat.
  Defined.

  Definition adjequiv_to_disp_nat_z_iso
             (τ : disp_adjoint_equivalence
                    (D := disp_bicat_comp_cat)
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
        (D := disp_bicat_comp_cat)
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
           exact disp_univalent_2_1_disp_bicat_comp_cat
         | ] ;
         use disp_nat_trans_eq ;
         intros x xx ;
         apply idpath).
  Defined.
End AdjEquivs.

Proposition fiberwise_univalent_2_0_disp_bicat_comp_cat
  : fiberwise_univalent_2_0 disp_bicat_comp_cat.
Proof.
  refine (λ (C : cat_with_terminal_cleaving) (χ₁ χ₂ : comprehension_functor C), _).
  use weqhomot.
  - exact (disp_nat_z_iso_weq_disp_adjequiv χ₁ χ₂
           ∘ disp_functor_eq_weq χ₁ χ₂ (disp_univalent_disp_codomain C)
           ∘ path_sigma_hprop _ _ _ (isaprop_is_cartesian_disp_functor _))%weq.
  - intro p ; cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      use (isaprop_disp_left_adjoint_equivalence
             _ _
             is_univalent_2_1_bicat_cat_with_terminal_cleaving).
      exact disp_univalent_2_1_disp_bicat_comp_cat.
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

Proposition disp_univalent_2_0_disp_bicat_comp_cat
  : disp_univalent_2_0 disp_bicat_comp_cat.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  exact fiberwise_univalent_2_0_disp_bicat_comp_cat.
Qed.

Proposition is_univalent_2_1_bicat_comp_cat
  : is_univalent_2_1 bicat_comp_cat.
Proof.
  use total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_1_disp_bicat_comp_cat.
Qed.

Proposition is_univalent_2_0_bicat_comp_cat
  : is_univalent_2_0 bicat_comp_cat.
Proof.
  use total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  - exact disp_univalent_2_0_disp_bicat_comp_cat.
Qed.

Proposition is_univalent_2_bicat_comp_cat
  : is_univalent_2 bicat_comp_cat.
Proof.
  split.
  - exact is_univalent_2_0_bicat_comp_cat.
  - exact is_univalent_2_1_bicat_comp_cat.
Qed.

(** * 5. Builders and accessors *)
Definition comp_cat
  : UU
  := bicat_comp_cat.

Definition make_comp_cat
           (C : cat_with_terminal_cleaving)
           (χ : comprehension_functor C)
  : comp_cat
  := C ,, χ.

Coercion comp_cat_to_cat_terminal_cleaving
         (C : comp_cat)
  : cat_with_terminal_cleaving
  := pr1 C.

Definition comp_cat_comprehension
           (C : comp_cat)
  : comprehension_functor C
  := pr2 C.

Definition comp_cat_functor
           (C₁ C₂ : comp_cat)
  : UU
  := C₁ --> C₂.

Definition make_comp_cat_functor
           {C₁ C₂ : comp_cat}
           (F : functor_with_terminal_cleaving C₁ C₂)
           (Fχ : comprehension_nat_trans
                   (comp_cat_comprehension C₁)
                   (comp_cat_comprehension C₂)
                   F)
  : comp_cat_functor C₁ C₂
  := F ,, Fχ.

Coercion comp_cat_functor_to_functor_with_terminal_cleaving
         {C₁ C₂ : comp_cat}
         (F : comp_cat_functor C₁ C₂)
  : functor_with_terminal_cleaving C₁ C₂
  := pr1 F.

Definition comp_cat_functor_comprehension
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
  : comprehension_nat_trans
      (comp_cat_comprehension C₁)
      (comp_cat_comprehension C₂)
      F
  := pr2 F.

Definition comp_cat_nat_trans
           {C₁ C₂ : comp_cat}
           (F G : comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Definition make_comp_cat_nat_trans
           {C₁ C₂ : comp_cat}
           {F G : comp_cat_functor C₁ C₂}
           (τ : nat_trans_with_terminal_cleaving F G)
           (Hτ : comprehension_nat_trans_eq
                   τ
                   (comp_cat_functor_comprehension F)
                   (comp_cat_functor_comprehension G))
  : comp_cat_nat_trans F G
  := τ ,, Hτ.

Coercion comp_cat_nat_trans_to_nat_trans_with_terminal_cleaving
         {C₁ C₂ : comp_cat}
         {F G : comp_cat_functor C₁ C₂}
         (τ : comp_cat_nat_trans F G)
  : nat_trans_with_terminal_cleaving F G
  := pr1 τ.

Definition comp_cat_nat_trans_comprehension
           {C₁ C₂ : comp_cat}
           {F G : comp_cat_functor C₁ C₂}
           (τ : comp_cat_nat_trans F G)
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

(** * 6. Comparison *)
Section ToCompCat.
  Context {C : univalent_category}
          (CC : comprehension_cat_structure C)
          (T : Terminal C)
          (HCC : is_univalent_disp (pr1 CC)).

  Definition comprehension_cat_structure_to_cat_with_terminal_disp_cat
    : cat_with_terminal_disp_cat.
  Proof.
    use make_cat_with_terminal_disp_cat.
    - exact C.
    - exact T.
    - use make_disp_univalent_category.
      + exact (pr1 CC).
      + exact HCC.
  Defined.

  Definition comprehension_cat_structure_to_cat_with_terminal_cleaving
    : cat_with_terminal_cleaving.
  Proof.
    use make_cat_with_terminal_cleaving.
    - exact comprehension_cat_structure_to_cat_with_terminal_disp_cat.
    - exact (pr12 CC).
  Defined.

  Definition comprehension_cat_structure_to_comp_cat
    : comp_cat.
  Proof.
    use make_comp_cat.
    - exact comprehension_cat_structure_to_cat_with_terminal_cleaving.
    - exact (pr122 CC ,, pr222 CC).
  Defined.
End ToCompCat.

Definition comp_cat_to_comprehension_cat_structure
           (C : comp_cat)
  : ∑ (C : univalent_category)
      (CC : comprehension_cat_structure C),
    Terminal C
    ×
    is_univalent_disp (pr1 CC).
Proof.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact C.
  - simple refine (_ ,, _ ,, _).
    + exact (disp_cat_of_types C).
    + exact (cleaving_of_types C).
    + exact (comp_cat_comprehension C).
  - exact (empty_context C).
  - exact (pr2 (disp_cat_of_types C)).
Defined.

Definition comp_cat_weq_comprehension_cat_structure
  : comp_cat
    ≃
    (∑ (C : univalent_category)
       (CC : comprehension_cat_structure C),
     Terminal C
     ×
     is_univalent_disp (pr1 CC)).
Proof.
  use weq_iso.
  - exact comp_cat_to_comprehension_cat_structure.
  - exact (λ CC, comprehension_cat_structure_to_comp_cat (pr12 CC) (pr122 CC) (pr222 CC)).
  - (**
     Note: the destructing below is necessary, because there are two inhabitants of the unit
     type in the definition `comp_cat`. By destructing everything this way, these inhabitants
     both become `tt`, and then the two terms become definitionally equal.
     *)
    abstract
      (intro C ;
       induction C as [ C χ ] ;
       induction C as [ C HD ] ;
       induction HD as [ HD a ] ;
       induction a ;
       induction C as [ C D ] ;
       induction D as [ T D ] ;
       induction T as [ T a ] ;
       induction a ;
       apply idpath).
  - abstract
      (intro C ;
       apply idpath).
Defined.

(** * 7. Adjoint equivalences *)
Section AdjequivIso.
  Context {C : cat_with_terminal_cleaving}
          {χ₁ χ₂ : comprehension_functor C}
          (τ : comprehension_nat_trans χ₁ χ₂ (id₁ _))
          (Hτ : ∏ (x : C)
                  (xx : disp_cat_of_types C x),
                is_z_iso_disp
                  (identity_z_iso _)
                  (τ x xx)).

  Definition to_adjequiv_disp_nat_trans
    : disp_nat_trans (nat_z_iso_id (functor_identity C)) χ₁ χ₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (x : C) (xx : disp_cat_of_types C x), τ x xx).
    - abstract
        (intros x y f xx yy ff ;
         use eq_cod_mor ;
         refine (maponpaths pr1 (disp_nat_trans_ax τ ff) @ _) ;
         refine (transportb_cod_disp _ _ _ @ _ @ !(transportb_cod_disp _ _ _)) ;
         apply idpath).
  Defined.

  Definition to_adjequiv_disp_nat_z_iso
    : disp_nat_z_iso χ₁ χ₂ (nat_z_iso_id (functor_identity _)).
  Proof.
    simple refine (_ ,, _).
    - exact to_adjequiv_disp_nat_trans.
    - intros x xx.
      apply Hτ.
  Defined.
End AdjequivIso.

Definition full_comp_cat_left_adjoint_equivalence_help
           {C₁ C₂ : cat_with_terminal_cleaving}
           (F : adjoint_equivalence C₁ C₂)
           (CC₁ : disp_bicat_comp_cat C₁)
           (CC₂ : disp_bicat_comp_cat C₂)
           (FF : CC₁ -->[ pr1 F ] CC₂)
           (HFF : ∏ (x : C₁)
                    (xx : disp_cat_of_types C₁ x),
                  is_z_iso_disp
                    (identity_z_iso _)
                    (pr1 FF x xx))
  : left_adjoint_equivalence
      (B := bicat_comp_cat)
      (a := C₁ ,, CC₁)
      (b := C₂ ,, CC₂)
      (pr1 F ,, FF).
Proof.
  revert C₁ C₂ F CC₁ CC₂ FF HFF.
  use J_2_0.
  - exact is_univalent_2_0_bicat_cat_with_terminal_cleaving.
  - intros C CC₁ CC₂ FF HFF.
    use (invmap (left_adjoint_equivalence_total_disp_weq _ _)).
    simple refine (_ ,, _).
    + apply internal_adjoint_equivalence_identity.
    + refine (transportf
                (λ z, disp_left_adjoint_equivalence _ z)
                _
                (pr2 (disp_nat_z_iso_to_adjequiv _ _ (to_adjequiv_disp_nat_z_iso FF HFF)))).
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      apply idpath.
Qed.

Definition comp_cat_left_adjoint_equivalence
           {C₁ C₂ : comp_cat}
           (F : comp_cat_functor C₁ C₂)
           (HF : left_adjoint_equivalence (pr1 F))
           (HFF : ∏ (x : C₁)
                    (xx : disp_cat_of_types C₁ x),
                  is_z_iso_disp
                    (identity_z_iso _)
                    (comp_cat_functor_comprehension F x xx))
  : left_adjoint_equivalence F.
Proof.
  use (full_comp_cat_left_adjoint_equivalence_help (pr1 F ,, HF)).
  exact HFF.
Defined.
