(** ** Precategories with homsets abelian groups (abgrops). *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.precategoriesWithBinOps.


Section def_precategory_with_abgrops.

  (** Definition of precategories such that homsets are abgrops. *)
  Definition PrecategoryWithAbgropsData (PB : precategoryWithBinOps) (hs : has_homsets PB) : UU :=
    Π (x y : PB), @isabgrop (hSetpair (PB⟦x,y⟧) (hs x y)) (to_binop x y).

  Definition PrecategoryWithAbgrops : UU :=
    Σ PA : (Σ PB : precategoryWithBinOps, has_homsets PB),
           PrecategoryWithAbgropsData (pr1 PA) (pr2 PA).

  Definition PrecategoryWithAbgrops_precategoryWithBinOps (PB : PrecategoryWithAbgrops) :
    precategoryWithBinOps := pr1 (pr1 PB).
  Coercion PrecategoryWithAbgrops_precategoryWithBinOps :
    PrecategoryWithAbgrops >-> precategoryWithBinOps.

  (* Precategory with abgrops to Precategory *)
  Definition PrecategoryWithAbgrops_Precategory (PWA : PrecategoryWithAbgrops) : Precategory.
  Proof.
    use tpair.
    - exact PWA.
    - exact (pr2 (pr1 PWA)).
  Defined.
  Coercion PrecategoryWithAbgrops_Precategory : PrecategoryWithAbgrops >-> Precategory.

  Definition mk_PrecategoryWithAbgrops (PB : precategoryWithBinOps) (hs : has_homsets PB)
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

  Definition to_runax (x y : PA) : isrunit op 1%multmonoid := runax (to_abgrop x y).

  Definition to_runax' (x y : PA) (f : x --> y) : to_binop x y f (to_unel x y) = f.
  Proof.
    apply to_runax.
  Qed.

  Definition to_inv {x y : PA} : PA⟦x, y⟧ -> PA⟦x, y⟧ := grinv (to_abgrop x y).

  Definition to_commax (x y : PA) := commax (to_abgrop x y).

  Definition to_commax' {x y : ob PA} (f g : x --> y) : to_binop x y f g = to_binop x y g f.
  Proof.
    apply to_commax.
  Qed.

  (** The following definition gives maps between abgrops homsets by precomposing and postcomposing
      with a morphism. Note that we have not required these to be abelian group morphisms of abelian
      groups. *)
  Definition to_premor {x y : PA} (z : PA) (f : x --> y) : to_abgrop y z -> to_abgrop x z :=
    fun (g : (to_abgrop y z)) => f ;; g.

  Definition to_postmor (x : PA) {y z : PA} (f : y --> z) : to_abgrop x y -> to_abgrop x z :=
    fun (g : (to_abgrop x y)) => g ;; f.


  (** Some equatios on inverses *)
  Lemma inv_inv_eq {x y : PA} (f : PA⟦x, y⟧) : to_inv (to_inv f) = f.
  Proof.
    unfold to_inv.
    apply (grinvinv (to_abgrop x y) f).
  Qed.

  Lemma cancel_inv {x y : PA} (f g : PA⟦x, y⟧) (H : (to_inv f) = (to_inv g)) : f = g.
  Proof.
    apply (grinvmaponpathsinv (to_abgrop x y) H).
  Qed.

  Lemma to_apply_inv {x y : PA} (f g : PA⟦x, y⟧) (H : f = g) : (to_inv f) = (to_inv g).
  Proof.
    apply maponpaths. apply H.
  Qed.

  Lemma to_inv_unel {x y : PA} : to_inv (to_unel x y) = to_unel x y.
  Proof.
    unfold to_unel.
    set (tmp := grinvunel (to_abgrop x y)). cbn in tmp. unfold to_inv.
    apply tmp.
  Qed.

  Lemma linvax {x y : PA} (f : PA⟦x, y⟧) : to_binop x y (to_inv f) f = to_unel x y.
  Proof.
    apply (grlinvax (to_abgrop x y)).
  Qed.

  Lemma rinvax {x y : PA} (f : PA⟦x, y⟧) : to_binop x y f (to_inv f) = to_unel x y.
  Proof.
    apply (grrinvax (to_abgrop x y)).
  Qed.

  Lemma to_lcan {x y : PA} {f g : PA⟦x, y⟧} (h : PA⟦x, y⟧) :
    to_binop x y h f = to_binop x y h g -> f = g.
  Proof.
    intros H.
    apply (grlcan (to_abgrop x y) h H).
  Qed.

  Lemma to_rcan {x y : PA} {f g : PA⟦x, y⟧} (h : PA⟦x, y⟧) :
    to_binop x y f h = to_binop x y g h -> f = g.
  Proof.
    intros H.
    apply (grrcan (to_abgrop x y) h H).
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
    apply (assocax (to_abgrop x y)).
  Qed.

  Lemma to_binop_inv_inv {x y : PA} (f g : PA⟦x, y⟧) :
    to_binop _ _ (to_inv f) (to_inv g) = to_inv (to_binop _ _ f g).
  Proof.
    apply (to_rcan g). rewrite to_assoc. rewrite linvax. rewrite to_runax'.
    apply (to_rcan f). rewrite to_assoc. rewrite linvax. cbn.
    rewrite <- (linvax (to_binop x y f g)). apply maponpaths. apply to_commax'.
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
Arguments to_inv [PA] [x] [y] _.
Arguments inv_inv_eq [PA] [x] [y] _.
Arguments cancel_inv [PA] [x] [y] _ _ _.


Section transport_morphisms.

  Variable PA : PrecategoryWithAbgrops.

  Lemma transportf_to_inv {x y z : ob PA} (f : x --> y) (e : y = z) :
    to_inv (transportf (precategory_morphisms x) e f) =
    transportf (precategory_morphisms x) e (to_inv f).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transportb_to_inv {x y z : ob PA} (f : y --> z) (e : x = y) :
    to_inv (transportb (fun x' : ob PA => precategory_morphisms x' z) e f) =
    transportb (fun x' : ob PA => precategory_morphisms x' z) e (to_inv f).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transportf_to_binop {x y z : ob PA} (f g : x --> y) (e : y = z) :
    to_binop _ _ (transportf (precategory_morphisms x) e f)
             (transportf (precategory_morphisms x) e g) =
    transportf (precategory_morphisms x) e (to_binop _ _ f g).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transportb_to_binop {x y z : ob PA} (f g : y --> z) (e : x = y) :
    to_binop _ _ (transportb (fun x' : ob PA => precategory_morphisms x' z) e f)
             (transportb (fun x' : ob PA => precategory_morphisms x' z) e g) =
    transportb (fun x' : ob PA => precategory_morphisms x' z) e (to_binop _ _ f g).
  Proof.
    induction e. apply idpath.
  Qed.

End transport_morphisms.
