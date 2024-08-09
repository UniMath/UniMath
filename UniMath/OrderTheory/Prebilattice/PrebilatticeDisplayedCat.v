(** Displayed category of pre-bilattices *)
(** Georgios V. Pitsiladis, Aug. 2024 - *)
Require Import UniMath.OrderTheory.Prebilattice.Prebilattice.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.

Definition respects_prebilattice_structure {X1 : hSet} {X2 : hSet} (b1 : prebilattice X1) (b2 : prebilattice X2) (f : X1 -> X2) : UU
:= ∀ x y,
  make_hProp _ (
               isapropdirprod _ _
                              (setproperty _  (meet b2 (f x) (f y)) (f (meet b1 x y)))
                              (isapropdirprod _ _ (setproperty _ (join b2 (f x) (f y)) (f (join b1 x y)))
                                              (isapropdirprod _ _
                                                              (setproperty _  (consensus b2 (f x) (f y)) (f (consensus b1 x y))  )
                                                              (setproperty _  (gullibility b2 (f x) (f y)) (f (gullibility b1 x y)))))
             ).

Lemma weqinv_respects_prebilattice_structure {X1 : hSet} {X2 : hSet} (b1 : prebilattice X1) (b2 : prebilattice X2) (f : weq X1 X2) (p : respects_prebilattice_structure b1 b2 f) : respects_prebilattice_structure b2 b1 (invmap f).
Proof.
intros x y.
do 3 (try use make_dirprod);
rewrite <- (homotweqinvweq f x), <- (homotweqinvweq f y);
[
  rewrite (pr1 (p (invmap f x) (invmap f y))) |
  rewrite (pr12 (p (invmap f x) (invmap f y))) |
  rewrite (pr122 (p (invmap f x) (invmap f y))) |
  rewrite (pr222 (p (invmap f x) (invmap f y)))
];
now rewrite homotweqinvweq,  homotweqinvweq, homotinvweqweq.
Qed.

Definition prebilattice_disp_category : category.
Proof.
use (@total_category hset_category).
use disp_cat_from_SIP_data.
- intro X.
  exact (prebilattice X).
- intros X1 X2 b1 b2 f.
  use (respects_prebilattice_structure b1 b2 f).
- intros X1 X2 b1 b2 f p1 p2.
  use impred_prop.
- now intros X1 b1 x y.
- intros X1 X2 X3 b1 b2 b3 f g p1 p2 x y.
  cbn.
  do 3 (try use make_dirprod).
  -- now rewrite (pr1 (p2 (f x) (f y))), (pr1 (p1 x y)).
  -- now rewrite (pr12 (p2 (f x) (f y))), (pr12 (p1 x y)).
  -- now rewrite (pr122 (p2 (f x) (f y))), (pr122 (p1 x y)).
  -- now rewrite (pr222 (p2 (f x) (f y))), (pr222 (p1 x y)).
Defined.

Lemma is_univalent_prebilattice_disp_category : is_univalent (prebilattice_disp_category) .
Proof.
use SIP.
- use Univalence.is_univalent_HSET.
- use isaset_prebilattice.
- intros X b1 b2 p1 p2.
  use prebilattice_eq; intro x; use weqfunextsec; intro y.
  -- exact (pr1 (p2 x y)).
  -- exact (pr12 (p2 x y)).
  -- exact (pr122 (p2 x y)).
  -- exact (pr222 (p2 x y)).
Defined.

Definition prebilattice_iso {X1 : hSet} {X2 : hSet} (b1 : prebilattice X1) (b2 : prebilattice X2) (f : weq X1 X2) (p : respects_prebilattice_structure b1 b2 f) : @z_iso prebilattice_disp_category (X1,,b1) (X2,,b2).
Proof.
set( f' := (pr1weq f,, p) : (prebilattice_disp_category ⟦ X1,, b1, X2,, b2 ⟧)%cat).
set (p_inv := weqinv_respects_prebilattice_structure b1 b2 f p).
exists f'.
exists (invmap f,, p_inv).
use make_dirprod.
- use total2_paths_f.
  -- use weqfunextsec.
     use homotinvweqweq.
  -- use weqfunextsec.
     intro x.
     use weqfunextsec.
     intro y.
     do 3 (try use dirprod_paths); use PartA.Unnamed_thm.
- use total2_paths_f.
  -- use weqfunextsec.
     use homotweqinvweq.
  -- use weqfunextsec.
     intro x.
     use weqfunextsec.
     intro y.
     do 3 (try use dirprod_paths); use PartA.Unnamed_thm.
Defined.

Definition prebilattice_transportf_iso {X1 : hSet} {X2 : hSet} (b1 : prebilattice X1) (b2 : prebilattice X2) (f : weq X1 X2) (p : respects_prebilattice_structure b1 b2 f) : ∑ p, transportf prebilattice p b1 = b2.
Proof.
  set (I := prebilattice_iso b1 b2 f p).
  set (i := fiber_paths (isotoid prebilattice_disp_category is_univalent_prebilattice_disp_category I)) .
  (* cbn in i. (* in order to see what path to use in the next line *)  *)
  exists ((base_paths (X1,, b1) (X2,, b2) (isotoid prebilattice_disp_category is_univalent_prebilattice_disp_category I))).
  exact i.
Defined.
