(** ****************************************************************************

The category of elements of a functor "F : C ⟶ HSET"

Contents:

- Category of elements ([cat_of_elems])
- Functoriality of the constructon of the category of elements
  ([cat_of_elems_on_nat_trans])
- The forgetful functor from the category of elements to C
  ([cat_of_elems_forgetful])

Originally written by: Dan Grayson
Ported to CT by: Anders Mörtberg

*******************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.

Local Open Scope cat.

Definition pointed_sets
  : category
  := total_category elements_universal.

Definition is_univalent_disp_elements_universal
  : is_univalent_disp elements_universal.
Proof.
  use is_univalent_disp_from_fibers.
  intros X x₁ x₂.
  use isweqimplimpl.
  - exact (λ p, pr1 p).
  - apply X.
  - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
    + apply X.
    + apply isaprop_is_iso_disp.
Qed.

Definition is_univalent_pointed_sets
  : is_univalent pointed_sets.
Proof.
  use is_univalent_total_category.
  - apply is_univalent_HSET.
  - exact is_univalent_disp_elements_universal.
Defined.

Definition pointed_sets_univalent
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact pointed_sets.
  - exact is_univalent_pointed_sets.
Defined.

Definition set_of_pointed_set
  : pointed_sets_univalent ⟶ HSET_univalent_category
  := pr1_category elements_universal.

Definition is_iso_pointed_sets
           {X Y : pointed_sets}
           (f : X --> Y)
           (Hf : is_iso (pr1 f))
  : is_iso f.
Proof.
  use is_iso_qinv.
  - simple refine (_ ,, _).
    + exact (inv_from_iso (make_iso _ Hf)).
    + abstract
        (cbn ;
         pose (pr2 f) as p ;
         cbn in p ;
         rewrite <- p ;
         exact (eqtohomot (iso_inv_after_iso (make_iso _ Hf)) (pr2 X))).
  - split.
    + abstract
        (use subtypePath ; [ intro ; apply (pr1 X) | ] ;
         exact (iso_inv_after_iso (make_iso _ Hf))).
    + abstract
        (use subtypePath ; [ intro ; apply (pr1 Y) | ] ;
         exact (iso_after_iso_inv (make_iso _ Hf))).
Defined.

Section CategoryOfElements.
  Context {C : category}
          (F : C ⟶ HSET).

  Definition disp_cat_of_elems_ob_mor
    : disp_cat_ob_mor C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ c, (F c : hSet)).
    - exact (λ c₁ c₂ x y f, #F f x = y).
  Defined.

  Definition disp_cat_of_elems_id_comp
    : disp_cat_id_comp C disp_cat_of_elems_ob_mor.
  Proof.
    split.
    - exact (λ c x, eqtohomot (functor_id F c) x).
    - refine (λ c₁ c₂ c₃ f g x₁ x₂ x₃ p q, _) ; cbn in *.
      refine (eqtohomot (functor_comp F f g) x₁ @ _) ; cbn.
      exact (maponpaths (# F g) p @ q).
  Qed.

  Definition disp_cat_of_elems_data
    : disp_cat_data C.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_elems_ob_mor.
    - exact disp_cat_of_elems_id_comp.
  Defined.

  Definition disp_mor_elems_isaprop
             {c₁ c₂ : C}
             (f : c₁ --> c₂)
             (x₁ : disp_cat_of_elems_data c₁)
             (x₂ : disp_cat_of_elems_data c₂)
    : isaprop (x₁ -->[ f ] x₂).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    cbn in *.
    apply (F c₂).
  Qed.

  Definition disp_cat_of_elems_axioms
    : disp_cat_axioms C disp_cat_of_elems_data.
  Proof.
    repeat split ; intros ; cbn.
    - apply disp_mor_elems_isaprop.
    - apply disp_mor_elems_isaprop.
    - apply disp_mor_elems_isaprop.
    - apply isasetaprop.
      apply disp_mor_elems_isaprop.
  Qed.

  Definition disp_cat_of_elems
    : disp_cat C.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_elems_data.
    - exact disp_cat_of_elems_axioms.
  Defined.

  Definition is_univalent_disp_disp_cat_of_elems
    : is_univalent_disp disp_cat_of_elems.
  Proof.
    use is_univalent_disp_from_fibers.
    intros c x₁ x₂.
    use isweqimplimpl.
    - intro f.
      exact (!(eqtohomot (functor_id F c) x₁) @ pr1 f).
    - apply (F c).
    - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
      + apply disp_mor_elems_isaprop.
      + apply isaprop_is_iso_disp.
  Qed.

  Definition is_iso_disp_cat_of_elems
             {c₁ c₂ : C}
             {f : iso c₁ c₂}
             {x : disp_cat_of_elems c₁}
             {y : disp_cat_of_elems c₂}
             (p : x -->[ f ] y)
    : is_iso_disp f p.
  Proof.
    simple refine (_ ,, (_ ,, _)) ; cbn in *.
    - rewrite <- p.
      refine (!(eqtohomot (functor_comp F f (inv_from_iso f)) x) @ _).
      rewrite iso_inv_after_iso.
      apply (eqtohomot (functor_id F c₁) x).
    - apply disp_mor_elems_isaprop.
    - apply disp_mor_elems_isaprop.
  Qed.

  Definition disp_cat_of_elems_is_opcartesian
             {c₁ c₂ : C}
             {f : c₁ --> c₂}
             {x₁ : disp_cat_of_elems c₁}
             {x₂ : disp_cat_of_elems c₂}
             (p : x₁ -->[ f ] x₂)
    : is_opcartesian p.
  Proof.
    intros c₃ x₃ g hh.
    use iscontraprop1.
    - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)) ; cbn -[isaprop].
      + apply disp_mor_elems_isaprop.
      + apply disp_cat_of_elems.
    - simple refine (_ ,, _) ; cbn in *.
      + refine (_ @ hh).
        refine (maponpaths (#F g) (!p) @ _).
        exact (!(eqtohomot (functor_comp F f g) x₁)).
      + apply disp_mor_elems_isaprop.
  Qed.

  Definition disp_cat_of_elems_opcleaving
    : opcleaving disp_cat_of_elems.
  Proof.
    intros c₁ c₂ x₁ f ; cbn in *.
    simple refine (_ ,, _ ,, _) ; cbn.
    - exact (#F f x₁).
    - apply idpath.
    - apply disp_cat_of_elems_is_opcartesian.
  Defined.

  Definition cat_of_elems_path_lift
             {x₁ x₂ : C}
             (p : x₁ = x₂)
             (y : disp_cat_of_elems x₂)
    : disp_cat_of_elems x₁.
  Proof.
    induction p.
    exact y.
  Defined.

  Definition cat_of_elems_path_path
             {x₁ x₂ : C}
             (p : x₁ = x₂)
             (y : disp_cat_of_elems x₂)
    : #F (idtoiso p) (cat_of_elems_path_lift p y) = y.
  Proof.
    induction p.
    cbn.
    exact (eqtohomot (functor_id F x₁) y).
  Qed.

  Definition cat_of_elems_path_natural
             {x₁ x₂ x₁' x₂' : C}
             (f₁ : x₁ --> x₁')
             (f₂ : x₂ --> x₂')
             (p : x₁ = x₂)
             (p' : x₁' = x₂')
             (y : disp_cat_of_elems x₂)
             (y' : disp_cat_of_elems x₂')
             (q : f₁ · idtoiso p' = idtoiso p · f₂)
             (r : y' = # F f₂ y)
    : cat_of_elems_path_lift p' y'
      =
      #F f₁ (cat_of_elems_path_lift p y).
  Proof.
    induction p, p'.
    cbn ; cbn in *.
    rewrite id_left, id_right in q.
    rewrite q.
    exact r.
  Qed.

  Section CatOfElemsIsoCleaving.
    Context (HC : is_univalent C)
            {x₁ x₂ : C}
            (f : x₁ --> x₂)
            (Hf : is_iso f)
            (y : disp_cat_of_elems x₂).

    Definition cat_of_elems_iso_lift
      : disp_cat_of_elems x₁
      := cat_of_elems_path_lift (isotoid _ HC (make_iso _ Hf)) y.

    Definition cat_of_elems_iso_path
      : #F f cat_of_elems_iso_lift = y.
    Proof.
      refine (_ @ cat_of_elems_path_path (isotoid _ HC (make_iso _ Hf)) y).
      apply maponpaths_2.
      rewrite idtoiso_isotoid.
      apply idpath.
    Qed.
  End CatOfElemsIsoCleaving.

  Definition cat_of_elems_iso_natural
             (HC : is_univalent C)
             {x₁ x₂ x₁' x₂' : C}
             (f₁ : x₁ --> x₁')
             (f₂ : x₂ --> x₂')
             (g₁ : x₁ --> x₂)
             (Hg₁ : is_iso g₁)
             (g₂ : x₁' --> x₂')
             (Hg₂ : is_iso g₂)
             (y : disp_cat_of_elems x₂)
             (y' : disp_cat_of_elems x₂')
             (q : f₁ · g₂ = g₁ · f₂)
             (r : y' = # F f₂ y)
    : cat_of_elems_iso_lift HC g₂ Hg₂ y'
      =
      #F f₁ (cat_of_elems_iso_lift HC g₁ Hg₁ y).
  Proof.
    use (cat_of_elems_path_natural f₁ f₂).
    rewrite !idtoiso_isotoid ; cbn.
    - exact q.
    - exact r.
  Qed.

  Definition cat_of_elems
    : category
    := total_category disp_cat_of_elems.

  Definition is_univalent_cat_of_elems
             (HC : is_univalent C)
    : is_univalent cat_of_elems.
  Proof.
    use is_univalent_total_category.
    - exact HC.
    - exact is_univalent_disp_disp_cat_of_elems.
  Defined.

  Definition is_iso_cat_of_elems
             {cx₁ cx₂ : cat_of_elems}
             (f : cx₁ --> cx₂)
             (Hf : is_iso (pr1 f))
    : is_iso f.
  Proof.
    use is_iso_qinv.
    - simple refine (inv_from_iso (make_iso _ Hf) ,, _).
      abstract
        (cbn ;
         pose (pr2 f) as p ;
         cbn in p ;
         rewrite <- p ;
         exact (eqtohomot
                  (iso_inv_after_iso
                     (functor_on_iso F (make_iso _ Hf))) (pr2 cx₁))).
    - split.
      + abstract
          (use subtypePath ; [ intro ; apply (F _) | ] ;
           apply (iso_inv_after_iso (make_iso _ Hf))).
      + abstract
          (use subtypePath ; [ intro ; apply (F _) | ] ;
           apply (iso_after_iso_inv (make_iso _ Hf))).
  Defined.

  Definition cat_of_elems_forgetful
    : cat_of_elems ⟶ C
    := pr1_category disp_cat_of_elems.

  Definition cat_of_elems_to_pointed_data
    : functor_data cat_of_elems pointed_sets.
  Proof.
    use make_functor_data.
    - exact (λ cx, F (pr1 cx) ,, pr2 cx).
    - exact (λ cx₁ cx₂ fp, #F (pr1 fp) ,, pr2 fp).
  Defined.

  Definition cat_of_elems_to_pointed_is_functor
    : is_functor cat_of_elems_to_pointed_data.
  Proof.
    split.
    - intros cx ; cbn in *.
      use subtypePath.
      {
        intro.
        apply (F _).
      }
      cbn.
      use funextsec.
      intro x.
      exact (eqtohomot (functor_id F (pr1 cx)) x).
    - intros cx₁ cx₂ cx₃ fp₁ fp₂ ; cbn in *.
      use subtypePath.
      {
        intro.
        apply (F _).
      }
      cbn.
      use funextsec.
      intro x.
      exact (eqtohomot (functor_comp F _ _) x).
  Qed.

  Definition cat_of_elems_to_pointed
    : cat_of_elems ⟶ pointed_sets.
  Proof.
    use make_functor.
    - exact cat_of_elems_to_pointed_data.
    - exact cat_of_elems_to_pointed_is_functor.
  Defined.

  Definition cat_of_elems_commute
    : cat_of_elems_to_pointed ∙ set_of_pointed_set
      ⟹
      cat_of_elems_forgetful ∙ F.
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros cx₁ cx₂ f ; cbn ;
         apply idpath).
  Defined.

  Definition cat_of_elems_commute_iso
    : nat_iso
        (cat_of_elems_to_pointed ∙ set_of_pointed_set)
        (cat_of_elems_forgetful ∙ F).
  Proof.
    use make_nat_iso.
    - exact cat_of_elems_commute.
    - intro.
      apply identity_is_iso.
  Defined.

  Section FunctorToCatOfElems.
    Context {C' : category}
            (G₁ : C' ⟶ pointed_sets)
            (G₂ : C' ⟶ C)
            (γ : nat_iso
                   (G₁ ∙ set_of_pointed_set)
                   (G₂ ∙ F)).

    Definition functor_to_cat_of_elems_data
      : functor_data C' cat_of_elems.
    Proof.
      use make_functor_data.
      - exact (λ c, G₂ c ,, γ c (pr2 (G₁ c))).
      - refine (λ c₁ c₂ f, # G₂ f ,, _).
        abstract
          (cbn ;
           refine (!(eqtohomot (nat_trans_ax γ _ _ f) (pr2 (G₁ c₁))) @ _) ; cbn ;
           apply maponpaths ;
           exact (pr2 (# G₁ f))).
    Defined.

    Definition functor_to_cat_of_elems_is_functor
      : is_functor functor_to_cat_of_elems_data.
    Proof.
      split.
      - intro x ; cbn.
        use subtypePath.
        {
          intro.
          apply (F _).
        }
        cbn.
        apply functor_id.
      - intros x y z f g ; cbn.
        use subtypePath.
        {
          intro.
          apply (F _).
        }
        cbn.
        apply functor_comp.
    Qed.

    Definition functor_to_cat_of_elems
      : C' ⟶ cat_of_elems.
    Proof.
      use make_functor.
      - exact functor_to_cat_of_elems_data.
      - exact functor_to_cat_of_elems_is_functor.
    Defined.

    Definition functor_to_cat_of_elems_pointed_nat_trans
      : functor_to_cat_of_elems ∙ cat_of_elems_to_pointed ⟹ G₁.
    Proof.
      use make_nat_trans.
      - refine (λ x, inv_from_iso (nat_iso_pointwise_iso γ x) ,, _) ; cbn.
        abstract
          (exact (eqtohomot
                    (iso_inv_after_iso
                       (nat_iso_pointwise_iso γ x))
                    (pr2 (G₁ x)))).
      - abstract
          (intros c₁ c₂ f ; cbn ;
           use subtypePath ;
             [ intro ;
               apply (pr1 (G₁ c₂))
             | ] ;
           cbn ;
           use funextsec ;
           intro x ;
           exact (eqtohomot (nat_trans_ax (nat_iso_inv_trans γ) _ _ f) x)).
    Defined.

    Definition functor_to_cat_of_elems_pointed
      : nat_iso
          (functor_to_cat_of_elems ∙ cat_of_elems_to_pointed)
          G₁.
    Proof.
      use make_nat_iso.
      - exact functor_to_cat_of_elems_pointed_nat_trans.
      - intro.
        use is_iso_pointed_sets.
        apply is_iso_inv_from_iso.
    Defined.

    Definition functor_to_cat_of_elems_forgetful_nat_trans
      : functor_to_cat_of_elems ∙ cat_of_elems_forgetful ⟹ G₂.
    Proof.
      use make_nat_trans.
      - exact (λ x, identity _).
      - abstract
          (intros x y f ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition functor_to_cat_of_elems_forgetful
      : nat_iso
          (functor_to_cat_of_elems ∙ cat_of_elems_forgetful)
          G₂.
    Proof.
      use make_nat_iso.
      - exact functor_to_cat_of_elems_forgetful_nat_trans.
      - intro.
        apply identity_is_iso.
    Defined.

    Definition functor_to_cat_of_elems_commute
               (c : C')
      : cat_of_elems_commute (functor_to_cat_of_elems c)
        =
        # set_of_pointed_set (functor_to_cat_of_elems_pointed_nat_trans c) · γ c.
    Proof.
      use funextsec.
      intro x ; cbn.
      exact (!(eqtohomot (iso_after_iso_inv (nat_iso_pointwise_iso γ c)) x)).
    Qed.
  End FunctorToCatOfElems.

  Section NatTransToCatOfElems.
    Context {C' : category}
            {G₁ G₂ : C' ⟶ cat_of_elems}
            (τ₁ : G₁ ∙ cat_of_elems_to_pointed
                  ⟹
                  G₂ ∙ cat_of_elems_to_pointed)
            (τ₂ : G₁ ∙ cat_of_elems_forgetful
                  ⟹
                  G₂ ∙ cat_of_elems_forgetful)
            (p : ∏ (x : C'),
                 # F (τ₂ x) (pr2 (G₁ x))
                 =
                 pr1 (τ₁ x) (pr2 (G₁ x))).

    Definition nat_trans_to_cat_of_elems
      : G₁ ⟹ G₂.
    Proof.
      use make_nat_trans.
      - simple refine (λ x, τ₂ x ,, _) ; cbn.
        abstract
          (exact (p x @ pr2 (τ₁ x))).
      - abstract
          (intros x y f ; cbn ;
           use subtypePath ; [ intro ; apply (F _) | ] ; cbn ;
           exact (nat_trans_ax τ₂ _ _ f)).
    Defined.
  End NatTransToCatOfElems.
End CategoryOfElements.

Definition univalent_cat_of_elems
           {C : univalent_category}
           (F : C ⟶ SET)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (cat_of_elems F).
  - apply is_univalent_cat_of_elems.
    apply C.
Defined.



(*
Section cat_of_elems_def.

Context {C : precategory} (X : C ⟶ HSET).

Definition cat_of_elems_ob_mor : precategory_ob_mor.
Proof.
exists (∑ (c : C), X c : hSet).
intros a b.
apply (∑ (f : C⟦pr1 a,pr1 b⟧), # X f (pr2 a) = pr2 b).
Defined.

Definition cat_of_elems_data : precategory_data.
Proof.
exists cat_of_elems_ob_mor.
split.
+ intros a.
  exists (identity (pr1 a)).
  abstract (exact (eqtohomot ((functor_id X) (pr1 a)) (pr2 a))).
+ intros a b c f g.
  exists (pr1 f · pr1 g).
  abstract (exact ((eqtohomot ((functor_comp X) (pr1 f) (pr1 g)) (pr2 a))
                      @ (maponpaths (# X (pr1 g)) (pr2 f) @ (pr2 g)))).
Defined.

Definition get_mor {x y : cat_of_elems_data} (f : _⟦x,y⟧) := pr1 f.

Lemma cat_of_elems_mor_eq (x y : cat_of_elems_data) (f g : _⟦x,y⟧) :
  get_mor f = get_mor g → f = g.
Proof.
intros p.
apply subtypePath.
- intro r; apply setproperty.
- exact p.
Qed.

Lemma is_precategory_cat_of_elems_data : is_precategory cat_of_elems_data.
Proof.
split; [split|split]; intros; apply cat_of_elems_mor_eq.
+ apply id_left.
+ apply id_right.
+ apply assoc.
+ apply assoc'.
Defined.

Definition cat_of_elems : precategory :=
  (cat_of_elems_data,,is_precategory_cat_of_elems_data).

Lemma has_homsets_cat_of_elems (hsC : has_homsets C) : has_homsets cat_of_elems.
Proof.
intros a b.
apply isaset_total2.
- apply hsC.
- intro f. apply isasetaprop, setproperty.
Qed.

End cat_of_elems_def.

Arguments get_mor {_ _ _ _} _.

(** Type as \int in Agda mode *)
Notation "∫ X" := (cat_of_elems X) (at level 3) : cat.

Section cat_of_elems_theory.

Context {C : precategory} {X Y : C ⟶ HSET}.

Definition get_ob (x : ∫ X) : C := pr1 x.
Definition get_el (x : ∫ X) : X (get_ob x) : hSet := pr2 x.
Definition get_eqn {x y : ∫ X} (f : (∫ X)⟦x,y⟧) :
  # X (get_mor f) (get_el x) = get_el y := pr2 f.

Definition make_ob (c : C) (x : X c : hSet) : ∫ X := (c,,x).
Definition make_mor (r s : ∫ X) (f : C⟦get_ob r,get_ob s⟧)
  (i : # X f (get_el r) = get_el s) : (∫ X)⟦r,s⟧ := (f,,i).


(** Functoriality of the construction of the category of elements *)
Definition cat_of_elems_on_nat_trans_data (α : X ⟹ Y) :
  functor_data (∫ X) (∫ Y).
Proof.
exists (λ a, (get_ob a,,α (get_ob a) (get_el a))).
intros b c f.
exists (get_mor f).
abstract (exact (!eqtohomot (pr2 α (get_ob b) (get_ob c) (get_mor f)) (get_el b)
                @ maponpaths (α (get_ob c)) (get_eqn f))).
Defined.

Lemma cat_of_elems_on_nat_trans_is_functor (α : X ⟹ Y) :
  is_functor (cat_of_elems_on_nat_trans_data α).
Proof.
split.
- now intros a; apply cat_of_elems_mor_eq.
- now intros a b c f g; apply cat_of_elems_mor_eq.
Qed.

Definition cat_of_elems_on_nat_trans (α : X ⟹ Y) : ∫ X ⟶ ∫ Y :=
  (cat_of_elems_on_nat_trans_data α,,cat_of_elems_on_nat_trans_is_functor α).

(* maybe make a functor [C,SET] ⟶ [category of Precategories] *)

(** The forgetful functor from the category of elements to C *)
Definition cat_of_elems_forgetful : ∫ X ⟶ C.
Proof.
use make_functor.
- exists pr1.
  intros a b; apply pr1.
- now split.
Defined.

Lemma reflects_isos_cat_of_elems_forgetful : reflects_isos cat_of_elems_forgetful.
Proof.
intros [c x] [d y] f Hf.
apply is_iso_from_is_z_iso.
assert (H := is_z_iso_from_is_iso _ Hf); clear Hf.
destruct f as [f i]; destruct H as [f' j].
assert (i' : #X f' y = x).
{ intermediate_path (#X f' (#X f x)).
  - exact (maponpaths (#X f') (!i)).
  - intermediate_path (#X (f' ∘ f) x).
    + exact (eqtohomot (!functor_comp X f f') x).
    + intermediate_path (#X (identity c) x).
      * exact (eqtohomot (maponpaths #X (pr1 j)) x).
      * exact (eqtohomot (functor_id X c) x).
}
exists (f' ,, i').
split; apply cat_of_elems_mor_eq; [ exact (pr1 j) | exact (pr2 j) ].
Qed.

End cat_of_elems_theory.
*)
