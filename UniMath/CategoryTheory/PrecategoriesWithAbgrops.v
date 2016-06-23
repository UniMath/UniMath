(** precategories enriched in abelian groups (abgrops). *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.

Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.


Section def_precategory_with_abgrops.


  (** Definition of precategories such that homsets are abgrops. *)
  Definition is_PrecategoryWithAbgrops (PB : PrecategoryWithBinOps)
             (hs : has_homsets PB) :=
    forall (x y : PB), @isabgrop (hSetpair (PB⟦x,y⟧) (hs x y))
                            (PrecategoryWithBinOps_binop PB x y).
  Definition mk_isPrecategoryWithAbgrosp (PB : PrecategoryWithBinOps)
             (hs : has_homsets PB)
    (H : forall (x y : PB), @isabgrop (hSetpair (PB⟦x,y⟧) (hs x y))
                                (PrecategoryWithBinOps_binop PB x y)) :
    is_PrecategoryWithAbgrops PB hs.
  Proof.
    intros x y.
    exact (H x y).
  Defined.

  Definition PrecategoryWithAbgrops : UU :=
    Σ PA : (Σ PB : PrecategoryWithBinOps, has_homsets PB),
           is_PrecategoryWithAbgrops (pr1 PA) (pr2 PA).
  Definition PrecategoryWithAbgrops_PrecategoryWithBinOps
             (PB : PrecategoryWithAbgrops) :
    PrecategoryWithBinOps := pr1 (pr1 PB).
  Coercion PrecategoryWithAbgrops_PrecategoryWithBinOps :
    PrecategoryWithAbgrops >-> PrecategoryWithBinOps.
  Definition mk_PrecategoryWithAbgrops (PB : PrecategoryWithBinOps)
             (hs : has_homsets PB)
             (H : is_PrecategoryWithAbgrops PB hs) : PrecategoryWithAbgrops.
  Proof.
    exact (tpair _ (tpair _ PB hs) H).
  Defined.


  Variable PA : PrecategoryWithAbgrops.

  (** Definitions to access the structure of a precategory with abelian
    groups. *)
  Definition PrecategoryWithAbgrops_homsets : has_homsets PA
    := pr2 (pr1 PA).
  Definition PrecategoryWithAbgrops_hset (x y : PA) : hSet
    := hSetpair (PA⟦x, y⟧) (PrecategoryWithAbgrops_homsets x y).
  Definition PrecategoryWIthAbgrops_setwithbinoppair (x y : PA)
    := setwithbinoppair (PrecategoryWithAbgrops_hset x y)
                        (PrecategoryWithBinOps_binop PA x y).
  Definition PrecategoryWithAbgrops_isabgrop (x y : PA)
    := (pr2 PA) x y.
  Definition PrecategoryWithAbgrops_abgrop (x y : PA) : abgr
    := abgrpair (PrecategoryWIthAbgrops_setwithbinoppair x y)
                (PrecategoryWithAbgrops_isabgrop x y).
  Definition PrecategoryWithAbgrops_unel (x y : PA)
    := unel (PrecategoryWithAbgrops_abgrop x y).
  Definition PrecategoryWithAbgrops_lunax (x y : PA)
    := lunax (PrecategoryWithAbgrops_abgrop x y).
  Definition PrecategoryWithAbgrops_runax (x y : PA)
    := runax (PrecategoryWithAbgrops_abgrop x y).
  Definition PrecategoryWithAbgrops_op (x y : PA)
    := @op (PrecategoryWithAbgrops_abgrop x y).

  (** The following definition gives maps between abgrops homsets by
    precomposing and postcomposing with a morphism. Note that we have
    not required these to be abelian group morphisms of abelian groups. *)
  Definition PrecategoryWithAbgrops_premor (x y z : PA) (f : x --> y) :
    PrecategoryWithAbgrops_abgrop y z -> PrecategoryWithAbgrops_abgrop x z
    := fun (g : (PrecategoryWithAbgrops_abgrop y z)) => f ;; g.
  Definition PrecategoryWithAbgrops_postmor (x y z : PA) (f : y --> z) :
    PrecategoryWithAbgrops_abgrop x y -> PrecategoryWithAbgrops_abgrop x z
    := fun (g : (PrecategoryWithAbgrops_abgrop x y)) => g ;; f.

End def_precategory_with_abgrops.
