(** ** Precategories with homsets abelian groups (abgrops). *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

Require Import UniMath.CategoryTheory.Core.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.

Section def_precategory_with_abgrops.

  (** Definition of precategories such that homsets are abgrops. *)
  Definition categoryWithAbgropsData (PB : precategoryWithBinOps) : UU :=
    ∏ (x y : PB), @isabgrop (make_hSet (PB⟦x,y⟧) (homset_property PB x y)) (@to_binop _ x y).

  Definition make_categoryWithAbgropsData {PB : precategoryWithBinOps}
             (H : ∏ (x y : PB), @isabgrop (make_hSet (PB⟦x,y⟧) (homset_property _  x y)) (@to_binop _ x y)) :
    categoryWithAbgropsData PB := H.

  Definition categoryWithAbgrops : UU :=
    ∑ PA : precategoryWithBinOps,
           categoryWithAbgropsData PA.


  Definition categoryWithAbgrops_precategoryWithBinOps (PB : categoryWithAbgrops) :
    precategoryWithBinOps := (pr1 PB).

  Coercion categoryWithAbgrops_precategoryWithBinOps :
    categoryWithAbgrops >-> precategoryWithBinOps.

  Definition make_categoryWithAbgrops (PB : precategoryWithBinOps)
             (H : categoryWithAbgropsData PB) : categoryWithAbgrops.
  Proof.
    exact (tpair _ PB H).
  Defined.


  Variable PA : categoryWithAbgrops.

  (** Definitions to access the structure of a precategory with abelian groups. *)
  Definition to_has_homsets : has_homsets PA := (pr1 PA).

  Definition to_homset (x y : PA) : hSet := make_hSet (PA⟦x, y⟧) (to_has_homsets x y).

  Definition to_setwithbinop (x y : PA) := make_setwithbinop (to_homset x y) (to_binop x y).

  Definition to_isabgrop (x y : PA) := (pr2 PA) x y.

  Definition to_abgr (x y : PA) : abgr := make_abgr (to_setwithbinop x y) (to_isabgrop x y).

  Definition to_unel (x y : PA) := unel (to_abgr x y).

  Definition to_lunax (x y : PA) := lunax (to_abgr x y).

  Definition to_lunax' (x y : PA) (f : x --> y) : to_binop x y (to_unel x y) f = f.
  Proof.
    apply to_lunax.
  Qed.

  Definition to_runax (x y : PA) : isrunit op 1%multmonoid := runax (to_abgr x y).

  Definition to_runax' (x y : PA) (f : x --> y) : to_binop x y f (to_unel x y) = f.
  Proof.
    apply to_runax.
  Qed.

  Definition to_inv {x y : PA} : PA⟦x, y⟧ -> PA⟦x, y⟧ := grinv (to_abgr x y).

  Definition to_commax (x y : PA) := commax (to_abgr x y).

  Definition to_commax' {x y : ob PA} (f g : x --> y) : to_binop x y f g = to_binop x y g f.
  Proof.
    apply to_commax.
  Qed.

  (** The following definition gives maps between abgrops homsets by precomposing and postcomposing
      with a morphism. Note that we have not required these to be abelian group morphisms of abelian
      groups. *)
  Definition to_premor {x y : PA} (z : PA) (f : x --> y) : to_abgr y z -> to_abgr x z :=
    fun (g : (to_abgr y z)) => f · g.

  Definition to_postmor (x : PA) {y z : PA} (f : y --> z) : to_abgr x y -> to_abgr x z :=
    fun (g : (to_abgr x y)) => g · f.

  (** Some equations on inverses *)
  Lemma inv_inv_eq {x y : PA} (f : PA⟦x, y⟧) : to_inv (to_inv f) = f.
  Proof.
    unfold to_inv.
    apply (grinvinv (to_abgr x y) f).
  Qed.

  Lemma cancel_inv {x y : PA} (f g : PA⟦x, y⟧) (H : (to_inv f) = (to_inv g)) : f = g.
  Proof.
    apply (grinvmaponpathsinv (to_abgr x y) H).
  Qed.

  Lemma to_inv_unel {x y : PA} : to_inv (to_unel x y) = to_unel x y.
  Proof.
    unfold to_unel.
    set (tmp := grinvunel (to_abgr x y)). cbn in tmp. unfold to_inv.
    apply tmp.
  Qed.

  Lemma linvax {x y : PA} (f : PA⟦x, y⟧) : to_binop x y (to_inv f) f = to_unel x y.
  Proof.
    apply (grlinvax (to_abgr x y)).
  Qed.

  Lemma rinvax {x y : PA} (f : PA⟦x, y⟧) : to_binop x y f (to_inv f) = to_unel x y.
  Proof.
    apply (grrinvax (to_abgr x y)).
  Qed.

  Lemma to_lcan {x y : PA} {f g : PA⟦x, y⟧} (h : PA⟦x, y⟧) :
    to_binop x y h f = to_binop x y h g -> f = g.
  Proof.
    intros H.
    apply (grlcan (to_abgr x y) h H).
  Qed.

  Lemma to_rcan {x y : PA} {f g : PA⟦x, y⟧} (h : PA⟦x, y⟧) :
    to_binop x y f h = to_binop x y g h -> f = g.
  Proof.
    intros H.
    apply (grrcan (to_abgr x y) h H).
  Qed.

  Lemma to_lrw {x y : PA} (f g h : PA⟦x, y⟧) (e : f = g) : to_binop x y f h = to_binop x y g h.
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma to_rrw {x y : PA} (f g h : PA⟦x, y⟧) (e : g = h) : to_binop x y f g = to_binop x y f h.
  Proof.
    apply maponpaths. exact e.
  Qed.

  Lemma to_assoc {x y : PA} (f g h : PA⟦x, y⟧) :
    to_binop _ _ (to_binop _ _ f g) h = to_binop _ _ f (to_binop _ _ g h).
  Proof.
    apply (assocax (to_abgr x y)).
  Qed.

  Lemma to_binop_inv_inv {x y : PA} (f g : PA⟦x, y⟧) :
    to_binop _ _ (to_inv f) (to_inv g) = to_inv (to_binop _ _ f g).
  Proof.
    apply (to_rcan g). rewrite to_assoc. rewrite linvax. rewrite to_runax'.
    apply (to_rcan f). rewrite to_assoc. rewrite linvax. cbn.
    rewrite <- (linvax (to_binop x y f g)). apply maponpaths. apply to_commax'.
  Qed.

  Lemma to_binop_inv_comm_1 {x y : PA} (f g : PA⟦x, y⟧) :
    to_binop _ _ (to_inv f) g = to_inv (to_binop _ _ f (to_inv g)).
  Proof.
    apply (to_rcan (to_binop x y f (to_inv g))). rewrite linvax.
    rewrite (to_commax' f). rewrite to_assoc. rewrite <- (to_assoc g).
    rewrite rinvax. rewrite to_lunax'. rewrite linvax. apply idpath.
  Qed.

  Lemma to_binop_inv_comm_2 {x y : PA} (f g : PA⟦x, y⟧) :
    to_binop _ _ f (to_inv g) = to_inv (to_binop _ _ (to_inv f) g).
  Proof.
    rewrite to_commax'. rewrite (to_commax' _ g). apply to_binop_inv_comm_1.
  Qed.

End def_precategory_with_abgrops.

Arguments to_has_homsets [PA] _ _ _ _ _ _.
Arguments to_homset [PA] _ _.
Arguments to_setwithbinop [PA] _ _.
Arguments to_isabgrop [PA] _ _.
Arguments to_abgr [PA] _ _.
Arguments to_unel [PA] _ _.
Arguments to_lunax [PA] _ _ _.
Arguments to_runax [PA] _ _ _.
Arguments to_premor [PA] [x] [y] _ _ _.
Arguments to_postmor [PA] _ [y] [z] _ _.
Arguments to_inv [PA] [x] [y] _.
Arguments inv_inv_eq [PA] [x] [y] _.
Arguments cancel_inv [PA] [x] [y] _ _ _.

Declare Scope abgrcat.
Delimit Scope abgrcat with abgrcat.
Notation "b <-- a" := (to_abgr a b) : abgrcat.
Notation "a --> b" := (to_abgr a b) : abgrcat.
Notation "1"     := (@identity (precategory_data_from_precategory (precategoryWithBinOps_precategory (categoryWithAbgrops_precategoryWithBinOps _))) _) : abgrcat.
Notation "0"     := (unel (grtomonoid (abgrtogr _))) : abgrcat.
Notation "0"     := (unel (grtomonoid (abgrtogr (to_abgr _ _)))) : abgrcat.
Notation "f + g" := (@op (pr1monoid (grtomonoid (abgrtogr _))) f g) : abgrcat.
Notation "f + g" := (@op (pr1monoid (grtomonoid (abgrtogr (to_abgr _ _)))) f g) : abgrcat.
Notation "  - g" := (@grinv (abgrtogr _) g) : abgrcat.
Notation "  - g" := (@grinv (abgrtogr (to_abgr _ _)) g) : abgrcat.
Notation "f - g" := (@op (pr1monoid (grtomonoid (abgrtogr _))) f (@grinv (abgrtogr (to_abgr _ _)) g)) : abgrcat.
Notation "f - g" := (@op (pr1monoid (grtomonoid (abgrtogr (to_abgr _ _)))) f (@grinv (abgrtogr (to_abgr _ _)) g)) : abgrcat.
Notation "g ∘ f" := (@compose (precategory_data_from_precategory (precategoryWithBinOps_precategory (categoryWithAbgrops_precategoryWithBinOps _))) _ _ _ f g) : abgrcat.
Notation "f · g" := (@compose (precategory_data_from_precategory (precategoryWithBinOps_precategory (categoryWithAbgrops_precategoryWithBinOps _))) _ _ _ f g) : abgrcat.
Notation "f = g" := (@eqset (pr1setwithbinop (pr1monoid (grtomonoid (abgrtogr (to_abgr _ _))))) f g) : abgrcat.

Section transport_morphisms.

  Variable PA : categoryWithAbgrops.

  Lemma transport_target_to_inv {x y z : ob PA} (f : x --> y) (e : y = z) :
    to_inv (transportf (precategory_morphisms x) e f) =
    transportf (precategory_morphisms x) e (to_inv f).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_source_to_inv {x y z : ob PA} (f : y --> z) (e : y = x) :
    to_inv (transportf (λ x' : ob PA, precategory_morphisms x' z) e f) =
    transportf (λ x' : ob PA, precategory_morphisms x' z) e (to_inv f).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_target_to_binop {x y z : ob PA} (f g : x --> y) (e : y = z) :
    to_binop _ _ (transportf (precategory_morphisms x) e f)
             (transportf (precategory_morphisms x) e g) =
    transportf (precategory_morphisms x) e (to_binop _ _ f g).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_source_to_binop {x y z : ob PA} (f g : y --> z) (e : y = x) :
    to_binop _ _ (transportf (λ x' : ob PA, precategory_morphisms x' z) e f)
             (transportf (λ x' : ob PA, precategory_morphisms x' z) e g) =
    transportf (λ x' : ob PA, precategory_morphisms x' z) e (to_binop _ _ f g).
  Proof.
    induction e. apply idpath.
  Qed.

End transport_morphisms.

Definition oppositeCategoryWithAbgrops (M : categoryWithAbgrops) : categoryWithAbgrops.
Proof.
  use tpair.
  - exact (oppositePrecategoryWithBinOps M).
  - exact (λ a b, @to_isabgrop M (rm_opp_ob b) (rm_opp_ob a)).
Defined.

Definition induced_categoryWithAbgrops (M : categoryWithAbgrops) {X:Type} (j : X -> ob M)
  : categoryWithAbgrops.
Proof.
  use tpair.
  - exact (induced_precategoryWithBinOps M j).
  - exact (λ a b, @to_isabgrop M (j a) (j b)).
Defined.
