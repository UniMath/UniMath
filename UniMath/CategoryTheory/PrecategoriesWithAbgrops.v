(** ** Precategories with homsets abelian groups (abgrops). *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.


Section def_precategory_with_abgrops.

  (** Definition of precategories such that homsets are abgrops. *)
  Definition PrecategoryWithAbgropsData (PB : PrecategoryWithBinOps) (hs : has_homsets PB) : UU :=
    Π (x y : PB), @isabgrop (hSetpair (PB⟦x,y⟧) (hs x y)) (to_binop x y).

  Definition PrecategoryWithAbgrops : UU :=
    Σ PA : (Σ PB : PrecategoryWithBinOps, has_homsets PB),
           PrecategoryWithAbgropsData (pr1 PA) (pr2 PA).

  Definition PrecategoryWithAbgrops_PrecategoryWithBinOps (PB : PrecategoryWithAbgrops) :
    PrecategoryWithBinOps := pr1 (pr1 PB).
  Coercion PrecategoryWithAbgrops_PrecategoryWithBinOps :
    PrecategoryWithAbgrops >-> PrecategoryWithBinOps.

  Definition mk_PrecategoryWithAbgrops (PB : PrecategoryWithBinOps) (hs : has_homsets PB)
             (H : PrecategoryWithAbgropsData PB hs) : PrecategoryWithAbgrops.
  Proof.
    exact (tpair _ (tpair _ PB hs) H).
  Defined.


  Variable PA : PrecategoryWithAbgrops.

  (** Definitions to access the structure of a precategory with abelian groups. *)
  Definition to_has_homsets : has_homsets PA := pr2 (pr1 PA).

  Definition to_homset (x y : PA) : hSet := hSetpair (PA⟦x, y⟧) (to_has_homsets x y).

  Definition to_setwithbinoppair (x y : PA) := setwithbinoppair (to_homset x y) (to_binop x y).

  Definition to_isabgrop (x y : PA) := (pr2 PA) x y.

  Definition to_abgrop (x y : PA) : abgr := abgrpair (to_setwithbinoppair x y) (to_isabgrop x y).

  Definition to_unel (x y : PA) := unel (to_abgrop x y).

  Definition to_lunax (x y : PA) := lunax (to_abgrop x y).

  Definition to_lunax' (x y : PA) (f : x --> y) : to_binop x y (to_unel x y) f = f.
  Proof.
    apply to_lunax.
  Qed.

  Definition to_runax (x y : PA) := runax (to_abgrop x y).

  Definition to_runax' (x y : PA) (f : x --> y) : to_binop x y f (to_unel x y) = f.
  Proof.
    apply to_runax.
  Qed.

  Definition to_inv (x y : PA) :  PA⟦x, y⟧ -> PA⟦x, y⟧ := grinv (to_abgrop x y).

  Definition to_commax (x y : PA) := commax (to_abgrop x y).

  (** The following definition gives maps between abgrops homsets by precomposing and postcomposing
      with a morphism. Note that we have not required these to be abelian group morphisms of abelian
      groups. *)
  Definition to_premor {x y : PA} (z : PA) (f : x --> y) : to_abgrop y z -> to_abgrop x z :=
    fun (g : (to_abgrop y z)) => f ;; g.

  Definition to_postmor (x : PA) {y z : PA} (f : y --> z) : to_abgrop x y -> to_abgrop x z :=
    fun (g : (to_abgrop x y)) => g ;; f.


  (** Some equatios on inverses *)
  Lemma inv_inv_eq {x y : PA} (f : PA⟦x, y⟧) : to_inv x y (to_inv x y f) = f.
  Proof.
    unfold to_inv.
    apply (grinvinv (to_abgrop x y) f).
  Qed.

  Lemma cancel_inv {x y : PA} (f g : PA⟦x, y⟧) (H : (to_inv  _ _ f) = (to_inv _ _ g)) : f = g.
  Proof.
    apply (grinvmaponpathsinv (to_abgrop x y) H).
  Qed.

  Lemma linvax {x y : PA} (f : PA⟦x, y⟧) : to_binop x y (to_inv x y f) f = to_unel x y.
  Proof.
    apply (grlinvax (to_abgrop x y)).
  Qed.

  Lemma rinvax {x y : PA} (f : PA⟦x, y⟧) : to_binop x y f (to_inv x y f) = to_unel x y.
  Proof.
    apply (grrinvax (to_abgrop x y)).
  Qed.

End def_precategory_with_abgrops.
Arguments to_has_homsets [PA] _ _ _ _ _ _.
Arguments to_homset [PA] _ _.
Arguments to_setwithbinoppair [PA] _ _.
Arguments to_isabgrop [PA] _ _.
Arguments to_abgrop [PA] _ _.
Arguments to_unel [PA] _ _.
Arguments to_lunax [PA] _ _ _.
Arguments to_runax [PA] _ _ _.
Arguments to_premor [PA] [x] [y] _ _ _.
Arguments to_postmor [PA] _ [y] [z] _ _.
Arguments to_inv [PA] _ _ _.
Arguments inv_inv_eq [PA] [x] [y] _.
Arguments cancel_inv [PA] [x] [y] _ _ _.
