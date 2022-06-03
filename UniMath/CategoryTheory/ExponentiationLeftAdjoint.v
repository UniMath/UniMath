(** ****************************************************************************

If a category C is small and has binary products then yoneda of any object is
tiny, that is, exponentiation by it has a right adjoint in the presheaf
category on C ([is_left_adjoint_exp_yoneda]).

The proof closely follows the one on page 10 of:

Internal Universes in Models of Homotopy Type Theory (2018)
Daniel R. Licata, Ian Orton, Andrew M. Pitts, Bas Spitters
https://arxiv.org/abs/1801.07664

In order to show that the exponential functor Yon(c) ⇒ _ has a right adjoint
we show that it is isomorphic to the functor given by precomposition by the
product functor c × _. The precomposition functor always has a right adjoint
given by right Kan extension. This isomorphism is constructed by a chain of
four isomorphisms at the set level. These are then lifted to an isomorphism
on the level of functors using that they are all natural.

We show that the exponential and precomposition with product functors are
isomorphic by the isomorphisms

 (Yon(c) → F) x ≅ Ĉ(Yon(x), Yon(c) → F)
                ≅ Ĉ(Yon(c) × Yon(x), F)
                ≅ Ĉ(Yon(c × x), F)
                ≅ ((c × _)* F) x

which are all natural in both F and x. This gives an isomorphism of the
functors. We show each functor isomorphism separately.

The three functors in the middle are denoted Fun1, Fun2 and Fun3 respectively.


Written by: Elisabeth Bonnevier, 2019

********************************************************************************)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.YonedaBinproducts.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.Presheaf.

Local Open Scope cat.

Section tiny_object_preshv.

Context {C : category} (PC : BinProducts C) (c : C).

Let prod_functor_c : functor C C := constprod_functor1 PC c.

Let Yon {C : category} : C ⟶ PreShv C := yoneda C.

Definition precomp_prod_functor : functor (PreShv C) (PreShv C).
Proof.
  use pre_composition_functor.
  apply functor_opp.
  exact prod_functor_c.
Defined.

Lemma precomp_prod_functor_has_right_adjoint : is_left_adjoint precomp_prod_functor.
Proof.
  apply RightKanExtension_from_limits.
  apply LimsHSET.
Defined.

Definition PreShv_exponentials : Exponentials (@BinProducts_PreShv C).
Proof.
  apply Exponentials_functor_HSET.
Defined.

Definition exp (F : PreShv C) : functor (PreShv C) (PreShv C) :=
  pr1 (PreShv_exponentials F).



(** The first isomorphism. Follows from the yoneda lemma. *)
Definition Fun1_functor_data : functor_data (PreShv C) (PreShv C).
Proof.
  use make_functor_data.
  - intro F.
    use functor_composite.
    + exact (PreShv C)^op.
    + use functor_opp.
      exact Yon.
    + exact (yoneda _ ((exp (Yon c)) F)).
  - intros F G α.
    use make_nat_trans.
    + intros X f.
      exact (f · (# (exp (Yon c)) α)).
    + intros X Y f.
      use funextsec; intro h.
      use assoc'.
Defined.

Lemma is_functor_Fun1 : is_functor Fun1_functor_data.
Proof.
  split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ set (idax := id_right f);
      rewrite <- (functor_id (exp (Yon c)) F) in idax;
      use idax
    | set (compax := assoc f (# (exp (Yon c)) α) (# (exp (Yon c)) β));
      rewrite <- (functor_comp (exp (Yon c)) α β) in compax;
      use compax ].
Qed.

Definition Fun1 : functor (PreShv C) (PreShv C) :=
  make_functor _ is_functor_Fun1.

Lemma first_iso_on_sets (F : PreShv C) (x : C) :
  z_iso (pr1 (Fun1 F) x) (pr1 ((exp (Yon c)) F) x).
Proof.
  use hset_equiv_z_iso.
  use yoneda_weq.
Defined.

Lemma first_iso_nat_in_x (F : PreShv C) :
  is_nat_trans (pr1 (Fun1 F)) _ (λ x, first_iso_on_sets F x).
Proof.
  use is_natural_yoneda_iso.
Qed.

Lemma first_iso_nat_in_F:
  is_nat_trans Fun1 (exp (Yon c))
    (λ F, make_nat_trans (pr1 (Fun1 F)) _ (first_iso_on_sets F) (first_iso_nat_in_x F)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros x.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros y.
  now apply funextsec.
Qed.

Lemma first_iso_on_functors : @z_iso [PreShv C, PreShv C] (exp (Yon c)) Fun1.
Proof.
  use z_iso_inv_from_z_iso.
  use make_PreShv_functor_z_iso.
  - intros F x.
    use first_iso_on_sets.
  - intro F.
    use first_iso_nat_in_x.
  - use first_iso_nat_in_F.
Defined.

(** The second isomorphism. Follows from the fact that the exponential functor
is right adjoint to the product functor. *)
Definition Fun2_functor_data : functor_data (PreShv C) (PreShv C).
Proof.
  use make_functor_data.
    - intro F.
      use functor_composite.
      + exact (PreShv C)^op.
      + use functor_opp.
        use functor_composite.
        * exact (PreShv C).
        * exact Yon.
        * exact (constprod_functor1 (@BinProducts_PreShv C) (Yon c)).
      + exact (Yon F).
    - intros F G α.
      use make_nat_trans.
      + intros X f.
        exact (f · α).
      + intros X Y f.
        use funextsec; intro g.
        use assoc'.
Defined.

Lemma is_functor_Fun2 : is_functor Fun2_functor_data.
Proof.
  split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ use id_right | use assoc ].
Qed.

Definition Fun2 : functor (PreShv C) (PreShv C) := make_functor _ is_functor_Fun2.

Lemma second_iso_on_sets (F : PreShv C) (x : C) :
  z_iso (pr1 (Fun1 F) x) (pr1 (Fun2 F) x).
Proof.
  use hset_equiv_z_iso.
  use invweq.
  use (adjunction_hom_weq (pr2 (PreShv_exponentials (Yon c)))).
Defined.

Lemma second_iso_nat_in_x (F : PreShv C) :
  is_nat_trans (pr1 (Fun1 F)) (pr1 (Fun2 F)) (λ x, second_iso_on_sets F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros ?.
  apply maponpaths; apply idpath.
Qed.

Lemma second_iso_nat_in_F :
  is_nat_trans Fun1 Fun2
               (λ F, make_nat_trans (pr1 (Fun1 F)) (pr1 (Fun2 F))
                                    (second_iso_on_sets F) (second_iso_nat_in_x F)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros h.
  apply (maponpaths (pr1 f x0)).
  apply (maponpaths (pr1 (pr1 g x0 (pr2 h)) x0)).
  now apply pathsdirprod; [use id_left|].
Qed.

Lemma second_iso_on_functors : @z_iso [PreShv C, PreShv C] Fun1 Fun2.
Proof.
  use make_PreShv_functor_z_iso.
  - intros F x.
    use second_iso_on_sets.
  - intro F.
    use second_iso_nat_in_x.
  - use second_iso_nat_in_F.
Defined.

(** The third isomorphism. Follows from the fact that the Yoneda functor
commutes with binary products. *)
Definition Fun3_functor_data : functor_data (PreShv C) (PreShv C).
Proof.
  use make_functor_data.
  - intro F.
    use functor_composite.
    + exact (PreShv C)^op.
    + use functor_opp.
      use functor_composite.
      * exact C.
      * exact (constprod_functor1 PC c).
      * exact Yon.
    + use Yon; apply F.
  - intros F G α.
    use make_nat_trans.
    + intros X f.
      exact (f · α).
    + intros X Y f.
      use funextsec; intro g.
      use assoc'.
Defined.

Lemma is_functor_Fun3 : is_functor Fun3_functor_data.
Proof.
   split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ use id_right | use assoc ].
Qed.

Definition Fun3 : functor (PreShv C) (PreShv C) := make_functor _ is_functor_Fun3.

Lemma third_iso_on_sets (F : PreShv C) (x : C) : z_iso (pr1 (Fun2 F) x) (pr1 (Fun3 F) x).
Proof.
  use hset_equiv_z_iso.
  use iso_comp_right_weq.
  use iso_yoneda_binproducts.
Defined.

Lemma third_iso_nat_in_x (F : PreShv C) :
  is_nat_trans (pr1 (Fun2 F)) (pr1 (Fun3 F)) (λ x, third_iso_on_sets F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  apply (nat_trans_eq has_homsets_HSET); intros x.
  apply funextsec; intros y.
  apply (maponpaths (pr1 g x)), pathsdirprod; cbn;
  unfold yoneda_morphisms_data, BinProduct_of_functors_mor; cbn.
  - now rewrite <- assoc, (BinProductOfArrowsPr1 _ (PC c X) (PC c Y)), id_right.
  - now rewrite <- !assoc, (BinProductOfArrowsPr2 _ (PC c X) (PC c Y)).
Qed.

Lemma third_iso_nat_in_F :
  is_nat_trans Fun2 Fun3
               (λ F, make_nat_trans (pr1 (Fun2 F)) (pr1 (Fun3 F))
                                    (third_iso_on_sets F) (third_iso_nat_in_x F)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros h.
  apply maponpaths; apply idpath.
Qed.

Lemma third_iso_on_functors : @z_iso [PreShv C, PreShv C] Fun2 Fun3.
Proof.
  use make_PreShv_functor_z_iso.
  - intros F x.
    use third_iso_on_sets.
  - intro F.
    use third_iso_nat_in_x.
  - use third_iso_nat_in_F.
Defined.


(** The fourth isomorphism. Follows from the yoneda lemma. *)
Lemma fourth_iso_on_sets (F : PreShv C) (x : C) :
  z_iso (pr1 (Fun3 F) x) (pr1 (precomp_prod_functor F) x).
Proof.
  use hset_equiv_z_iso.
  use yoneda_weq.
Defined.

Lemma fourth_iso_nat_in_x (F : PreShv C) :
  is_nat_trans (pr1 (Fun3 F)) _ (λ x, fourth_iso_on_sets F x).
Proof.
  intros X Y f.
  use (is_natural_yoneda_iso _ _ _ _  (BinProduct_of_functors_mor _ _ PC _ _ _ _ _)).
Qed.

Lemma fourth_iso_nat_in_F:
  is_nat_trans Fun3 precomp_prod_functor
    (λ F, make_nat_trans (pr1 (Fun3 F)) _ (fourth_iso_on_sets F) (fourth_iso_nat_in_x F)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply idpath.
Qed.

Lemma fourth_iso_on_functors : @z_iso [(PreShv C), (PreShv C)] Fun3 precomp_prod_functor.
Proof.
  use make_PreShv_functor_z_iso.
  - intros F x.
    use fourth_iso_on_sets.
  - intro F.
    use fourth_iso_nat_in_x.
  - use fourth_iso_nat_in_F.
Defined.

(** The exponential functor and the precomposition functor are isomorphic. *)
Lemma iso_exp_precomp_prod_functor : @z_iso [PreShv C, PreShv C] precomp_prod_functor (exp (Yon c)).
Proof.
  use z_iso_inv_from_z_iso.
  use (z_iso_comp first_iso_on_functors).
  use (z_iso_comp second_iso_on_functors).
  use (z_iso_comp third_iso_on_functors).
  use fourth_iso_on_functors.
Defined.

(** The exponential functor has a right adjoint. *)
Theorem is_left_adjoint_exp_yoneda : is_left_adjoint (exp (Yon c)).
Proof.
  use is_left_adjoint_z_iso.
  - exact precomp_prod_functor.
  - use iso_exp_precomp_prod_functor.
  - use precomp_prod_functor_has_right_adjoint.
Defined.

End tiny_object_preshv.
