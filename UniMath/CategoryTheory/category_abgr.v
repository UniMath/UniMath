(* The category abelian groups. *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Basics.UnivalenceAxiom.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.Foundations.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.HLevel_n_is_of_hlevel_Sn.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.


(** In this section we construct the category of abelian groups. *)
Section ABGR_precategory.

  Definition abgr_fun_space (A B : abgr) : hSet :=
    hSetpair _ (isasetmonoidfun A B).

  Definition abgr_precategory_ob_mor : precategory_ob_mor :=
    tpair (fun ob : UU => ob -> ob -> UU) abgr
          (fun A B : abgr => abgr_fun_space A B).

  Definition idabgrfun (A : abgr) : monoidfun A A.
  Proof.
    use monoidfunconstr. intros a. exact a.
    split.
    intros a a'.
    apply idpath.
    apply idpath.
  Defined.

  Definition idabgrfun_remove_left (A B : abgr) (f : monoidfun A B) :
    monoidfuncomp (idabgrfun A) f = f.
  Proof.
    unfold monoidfuncomp. unfold idabgrfun.
    use total2_paths. cbn. unfold funcomp. apply maponpaths.
    apply idpath. apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  Definition idabgrfun_remove_right (A B : abgr) (f : monoidfun A B) :
    monoidfuncomp f (idabgrfun B) = f.
  Proof.
    unfold monoidfuncomp, idabgrfun.
    use total2_paths. cbn. unfold funcomp. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  Definition abgrfuncomp_assoc (A B C D : abgr) (f : monoidfun A B)
             (g : monoidfun B C) (h : monoidfun C D) :
    monoidfuncomp (monoidfuncomp f g) h = monoidfuncomp f (monoidfuncomp g h).
  Proof.
    unfold monoidfuncomp. apply maponpaths.
    apply isapropismonoidfun.
  Defined.

  Definition abgr_precategory_data : precategory_data :=
    precategory_data_pair abgr_precategory_ob_mor
                          (fun (A : abgr) => idabgrfun A )
                          (fun (A B C : abgr) (f : monoidfun A B)
                             (g : monoidfun B C) => monoidfuncomp f g).

  Lemma is_precategory_abgr_precategory_data :
    is_precategory abgr_precategory_data.
  Proof.
    repeat split; simpl.

    intros a b f. apply idabgrfun_remove_left.
    intros a b f. apply idabgrfun_remove_right.

    intros a b c d f g h. apply pathsinv0.
    apply (abgrfuncomp_assoc a b c d f g h).
  Qed.

  Definition abgr_precategory : precategory :=
    tpair _ _ is_precategory_abgr_precategory_data.

  Local Notation ABGR := abgr_precategory.
  Lemma has_homsets_ABGR : has_homsets ABGR.
  Proof. intros a b; apply isasetmonoidfun. Qed.

End ABGR_precategory.

Notation ABGR := abgr_precategory.

Section ABGR_category.

  (** ** Equivalence between isomorphisms and monoidisos *)

  Lemma abgr_iso_is_equiv (A B : ob ABGR)
        (f : iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    apply (gradth _ (pr1monoidfun _ _ (inv_from_iso f))).
    - intro x.
      set (T:=iso_inv_after_iso f).
      apply subtypeInjectivity in T.
      set (T':=toforallpaths _ _ _ T). apply T'.
      intro x0.
      apply isapropismonoidfun.
    - intros y.

      set (T:=iso_after_iso_inv f).
      apply subtypeInjectivity in T.
      set (T':=toforallpaths _ _ _ T). apply T'.
      intros x0.
      apply isapropismonoidfun.
  Defined.

  Lemma abgrp_iso_equiv (A B : ob ABGR) :
    iso A B -> monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B).
  Proof.
    intro f.
    use monoidisopair.
    set (X := abgr_iso_is_equiv A B f).
    apply (weqpair (pr1 (pr1 f)) X).
    apply (pr2 (pr1 f)).
  Defined.

  Lemma abgr_equiv_is_iso (A B : abgr) (f : monoidiso A B) :
    @is_isomorphism ABGR A B (monoidfunconstr (pr2 f)).
  Proof.
    apply (is_iso_qinv (C:=ABGR) _ (monoidfunconstr (pr2 (invmonoidiso f)))).
    split; cbn. unfold monoidfuncomp, compose, idabgrfun, identity.
    use total2_paths. cbn. apply funextfun. intros x.
    apply homotinvweqweq. cbn. use total2_paths. cbn.
    apply proofirrelevance. apply isapropisbinopfun.
    apply proofirrelevance.  apply (pr2 (pr1 (pr1 A))).

    use total2_paths. cbn. apply funextfun. intros x.
    apply homotweqinvweq. cbn. apply proofirrelevance.
    apply isapropismonoidfun.
  Defined.

  Lemma abgr_equiv_iso (A B : ABGR) :
    monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B) -> iso A B.
  Proof.
    intro f.
    cbn in *.
    set (T := abgr_equiv_is_iso A B f).
    set (T' := @isopair ABGR _ _ (monoidfunconstr (pr2 f)) T).
    apply T'.
  Defined.

  Lemma abgrp_iso_equiv_is_equiv (A B : ABGR) : isweq (abgrp_iso_equiv A B).
  Proof.
    apply (gradth _ (abgr_equiv_iso A B)).
    intro; apply eq_iso. apply maponpaths.
    unfold abgr_equiv_iso, abgrp_iso_equiv. cbn.
    use total2_paths. cbn. unfold monoidfunconstr.
    apply subtypeEquality. intros y. apply isapropismonoidfun.
    apply maponpaths. apply subtypeEquality.
    unfold isPredicate.

    intros x0. apply isapropismonoidfun.
    apply idpath.

    apply proofirrelevance.
    apply isaprop_is_iso.

    intros y. unfold abgrp_iso_equiv, abgr_equiv_iso. cbn.
    use total2_paths. cbn. unfold monoidfunconstr.
    apply subtypeEquality. intros x. apply isapropisweq.
    apply idpath.

    apply proofirrelevance.
    apply isapropismonoidfun.
  Defined.

  Definition abgr_iso_equiv_weq (A B : ABGR) :
    weq (iso A B) (monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B)).
  Proof.
    exists (abgrp_iso_equiv A B).
    apply abgrp_iso_equiv_is_equiv.
  Defined.

  Lemma abgr_equiv_iso_is_equiv (A B : ABGR) : isweq (abgr_equiv_iso A B).
  Proof.
    apply (gradth _ (abgrp_iso_equiv A B)).
    intros x. apply subtypeEquality.
    intros y. apply isapropismonoidfun.

    unfold abgr_equiv_iso, abgrp_iso_equiv. cbn.
    use total2_paths. cbn. apply idpath.
    apply isapropisweq.

    intros y. unfold abgr_equiv_iso, abgrp_iso_equiv. cbn.
    use total2_paths. cbn. unfold monoidfunconstr. cbn.
    apply subtypeEquality. intros x. apply isapropismonoidfun.
    apply idpath. apply proofirrelevance.
    apply isaprop_is_iso.
  Qed.

  Definition hbinop_equiv_iso_weq (A B : ABGR) :
    weq (monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B)) (iso A B).
  Proof.
    exists (abgr_equiv_iso A B).
    apply abgr_equiv_iso_is_equiv.
  Defined.


(** ** HERE ONE SHOULD ADD A PROOF THAT ABGR IS ACTUALLY A CATEGORY.
         See category_hset.v *)

End ABGR_category.


(** ** Zero object in ABGR
  In the following section we prove that the category of abelian groups has
  a zero object.
 *)
Section ABGR_zero.

  (** The zero object we use consists of one element, the unit element. *)
  Definition ABGR_zero : abgr.
  Proof.
    use abgrpair.
    use setwithbinoppair.
    exact unitset.
    unfold binop.
    exact (fun i i': unitset => i).

    (* isabgrop *)
    unfold isabgrop. split.

    use isgroppair. split.

    unfold isassoc. intros x x' x''.
    unfold op. cbn. apply idpath.
    use isunitalpair. cbn. exact tt.

    unfold isunit. split.
    unfold islunit. intros x. cbn. apply isconnectedunit.
    unfold isrunit. intros x. cbn. apply isconnectedunit.

    unfold invstruct. cbn. use (tpair _ (fun _ : unit => tt)).
    cbn. unfold isinv. split.
    unfold islinv. intros X. apply idpath.
    unfold isrinv. intros x. apply isconnectedunit.

    unfold iscomm. intros x x'. unfold op. cbn.
    apply isconnectedunit.
  Defined.

  (** Construction of the morphism to the zero object. *)
  Definition ABGR_zero_from (A : abgr) : ABGR⟦A, ABGR_zero⟧.
  Proof.
    use monoidfunconstr.
    exact (fun _ : A => tt).
    unfold ismonoidfun. unfold isbinopfun. cbn. split.
    intros x x'. apply idpath.
    apply idpath.
  Defined.

  (** Construction of the morphisms from the zero object. *)
  Definition ABGR_zero_to (A : abgr) : ABGR⟦ABGR_zero, A⟧.
  Proof.
    use monoidfunconstr.
    exact (fun _ : ABGR_zero => unel A).
    unfold ismonoidfun. unfold isbinopfun. cbn. split.
    intros x x'. rewrite (runax A). apply idpath.
    apply idpath.
  Defined.

  Definition ABGR_zero_arrow (A B : abgr) : ABGR⟦A, B⟧.
  Proof.
    use monoidfunconstr.
    exact (fun _ : A => unel B).
    unfold ismonoidfun. unfold isbinopfun. cbn. split.
    intros x x'. rewrite (runax B). apply idpath.
    apply idpath.
  Defined.

  (** The following lemma constructs a zero object in ABGR. *)
  Lemma ABGR_has_zero : Zero ABGR.
  Proof.
    use mk_Zero.
    exact ABGR_zero.
    use mk_isZero.
    intros a. refine (tpair _ (ABGR_zero_to a) _).
    intros t. use total2_paths. apply funextfun. intros x.

    rewrite (isconnectedunit x tt). apply (pr2 (pr2 t)).
    apply proofirrelevance. apply isapropismonoidfun.

    intros a. refine (tpair _ (ABGR_zero_from a) _).
    intros t. use total2_paths. apply funextfun. intros x.
    apply isconnectedunit.
    apply proofirrelevance. apply isapropismonoidfun.
  Defined.


  (** The following lemmas verify that the above definition behaves as
    expected. *)
  Lemma ABGR_has_zero_ob : ZeroObject (ABGR_has_zero) = ABGR_zero.
  Proof.
    apply idpath.
  Qed.

  Lemma ABGR_has_zero_from ( A : abgr ) :
    @ZeroArrowFrom ABGR ABGR_has_zero A = ABGR_zero_to A.
  Proof.
    apply idpath.
  Qed.

  Lemma ABGR_has_zero_to (A : abgr ) :
    @ZeroArrowTo ABGR ABGR_has_zero A = ABGR_zero_from A.
  Proof.
    apply idpath.
  Qed.

  Lemma ABGR_has_zero_arrow_eq (A B : abgr) :
    @ZeroArrow ABGR ABGR_has_zero A B = ABGR_zero_arrow A B.
  Proof.
    use total2_paths. cbn. unfold funcomp. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

End ABGR_zero.


(** ** ABGR is PreAdditive
  In the following section we prove that the category of abelian groups is
  preadditive. *)
Section ABGR_preadditive.

  (** Cancellation of binary operation from left and from right. *)
  Lemma cancel_lop (X : setwithbinop) (x y z : X) :
    x = y -> @op X z x = @op X z y.
  Proof.
    intros e. induction e. apply idpath.
  Qed.

  Lemma cancel_rop (X : setwithbinop) (x y z : X) :
    x = y -> @op X x z = @op X y z.
  Proof.
    intros e. induction e. apply idpath.
  Qed.

  (** The binop structure on the category of abelian groups. *)
  Definition ABGR_hombinop (X Y : ABGR) :
    ABGR⟦X, Y⟧ -> ABGR⟦X, Y⟧ -> ABGR⟦X, Y⟧.
  Proof.
    intros f g.
    use monoidfunconstr.
    exact (fun x : (abgrtoabmonoid X) =>
             @op (abgrtoabmonoid Y) ((pr1 f) x) ((pr1 g) x)).
    split.

    intros x x'.
    rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 g)).
    repeat rewrite <- (assocax (abgrtoabmonoid Y)). apply cancel_rop.
    repeat rewrite (assocax (abgrtoabmonoid Y)). apply cancel_lop.
    apply (pr2 (pr2 Y)).

    rewrite (pr2 (pr2 f)). rewrite (pr2 (pr2 g)).
    apply (runax (abgrtoabmonoid Y)).
  Defined.

  (** The morphism which maps everything to unit element.
    This is actually the zero morphism. *)
  Definition ABGR_hombinop_unel (X Y : ABGR) : ABGR⟦X, Y⟧.
  Proof.
    use monoidfunconstr.
    exact (fun x : (pr1 X) => unel (abgrtoabmonoid Y)).
    split.

    intros x x'. apply pathsinv0. apply (runax (abgrtoabmonoid Y)).
    apply idpath.
  Defined.

  (** Verification of the unit axioms for the above morphism. *)
  Definition ABGR_hombinop_runax (X Y : ABGR) (f : ABGR⟦X, Y⟧) :
    ABGR_hombinop X Y f (ABGR_hombinop_unel X Y) = f.
  Proof.
    use total2_paths. cbn. apply funextfun. intros x.
    rewrite (runax (abgrtoabmonoid Y)). apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.


  Definition ABGR_hombinop_lunax (X Y : ABGR) (f : ABGR⟦X, Y⟧) :
    ABGR_hombinop X Y (ABGR_hombinop_unel X Y) f = f.
  Proof.
    use total2_paths. cbn. apply funextfun. intros x.
    rewrite (lunax (abgrtoabmonoid Y)). apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Commutativity of the binary operation. *)
  Definition ABGR_hombinop_comm (X Y : ABGR) :
    Π (f g : ABGR⟦X, Y⟧),
      @ABGR_hombinop X Y f g = @ABGR_hombinop X Y g f.
  Proof.
    intros f g. use total2_paths. cbn. apply funextfun. intros x.
    rewrite (pr2 (pr2 Y)). apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  (** How operation behaves under the inverse function. *)
  Lemma grinvcomp (Y : gr) :
    Π y1 y2 : Y, grinv Y (@op Y y1 y2) = @op Y (grinv Y y2) (grinv Y y1).
  Proof.
    intros y1 y2.
    apply (grrcan Y y1).
    rewrite (assocax Y). rewrite (grlinvax Y). rewrite (runax Y).
    apply (grrcan Y y2).
    rewrite (grlinvax Y). rewrite (assocax Y). rewrite (grlinvax Y).
    apply idpath.
  Qed.


  (** Construction of the inverse function in the category of abelian groups. *)
  Definition ABGR_hombinop_inv (X Y : ABGR) : ABGR⟦X, Y⟧ -> ABGR⟦X, Y⟧.
  Proof.
    intros f.
    use monoidfunconstr.
    exact (fun x : (abgrtoabmonoid X) => grinv (abgrtogr Y) ((pr1 f) x)).
    split.

    intros x x'.
    rewrite (pr1 (pr2 f)). rewrite (pr2 (pr2 Y)).
    rewrite (grinvcomp (abgrtogr Y)).
    apply idpath.

    rewrite (pr2 (pr2 f)).
    apply (grinvunel (abgrtogr Y)).
  Defined.

  (** Verification that this gives left and right inverse. *)
  Definition ABGR_hombinop_linvax (X Y : ABGR) :
    Π f : ABGR⟦X, Y⟧, ABGR_hombinop X Y (ABGR_hombinop_inv X Y f) f
                      = ABGR_hombinop_unel X Y.
  Proof.
    intros f. use total2_paths. cbn. apply funextfun. intros x.
    apply (grlinvax (abgrtogr Y)).

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.


  Definition ABGR_hombinop_rinvax (X Y : ABGR) :
    Π f : ABGR⟦X, Y⟧, ABGR_hombinop X Y f (ABGR_hombinop_inv X Y f)
                      = ABGR_hombinop_unel X Y.
  Proof.
    intros f. use total2_paths. cbn. apply funextfun. intros x.
    apply (grrinvax (abgrtogr Y)).

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Associativity of the binary operation. *)
  Definition ABGR_hombinop_assoc (X Y : ABGR) (f g h : ABGR⟦X, Y⟧) :
    ABGR_hombinop X Y f (ABGR_hombinop X Y g h) =
    ABGR_hombinop X Y (ABGR_hombinop X Y f g) h.
  Proof.
    use total2_paths. cbn. apply funextfun. intros x.
    rewrite (assocax (abgrtoabmonoid Y)).
    apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  (** WithBinOpsData *)
  Definition ABGR_WithBinOpsData : PrecategoryWithBinOpsData ABGR.
  Proof.
    unfold PrecategoryWithBinOpsData.
    intros X Y.
    exact (ABGR_hombinop X Y).
  Defined.

  Definition ABGR_WithBinOps : PrecategoryWithBinOps
    := tpair _ ABGR ABGR_WithBinOpsData.

  (** WithAbgrops *)
  Definition ABGR_WithAbGrops : PrecategoryWithAbgrops.
  Proof.
    use (mk_PrecategoryWithAbgrops ABGR_WithBinOps has_homsets_ABGR).
    intros X Y.
    split.

    use isgroppair.
    split.

    (* Associativity *)
    intros x y z.
    apply pathsinv0. apply ABGR_hombinop_assoc.

    (* Unit *)
    use isunitalpair.
    apply ABGR_hombinop_unel.
    split.
    unfold islunit. intros x. apply (ABGR_hombinop_lunax X Y).
    unfold isrunit. intros x. apply (ABGR_hombinop_runax X Y).

    (* invstruct *)
    use tpair.
    exact (ABGR_hombinop_inv X Y).
    cbn.
    split.
    intros f.
    apply ABGR_hombinop_linvax.
    intros f.
    apply ABGR_hombinop_rinvax.

    (* Commutativity *)
    intros f g. apply (ABGR_hombinop_comm X Y f g).
  Defined.

  (** Finally, we prove that the category of abelian groups is preadditive. *)
  Definition ABGR_PreAdditive : PreAdditive.
  Proof.
    use mk_PreAdditive.
    exact (ABGR_WithAbGrops).

    use mk_isPreAdditive.

    (* First bilinearity. *)
    intros X Y Z f.
    split.

    intros g h.
    unfold PrecategoryWithAbgrops_premor.
    use total2_paths. cbn. apply funextfun.
    intros x. unfold funcomp. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    unfold PrecategoryWithAbgrops_premor.
    use total2_paths. cbn. apply funextfun.
    intros x. unfold funcomp. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* Second bilinearity. *)
    intros X Y Z f.
    split.

    intros g h.
    unfold PrecategoryWithAbgrops_premor.
    use total2_paths. cbn. apply funextfun.
    intros x. unfold funcomp. rewrite (pr1 (pr2 f)) . apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    unfold PrecategoryWithAbgrops_premor.
    use total2_paths. cbn. apply funextfun.
    intros x. unfold funcomp. apply (pr2 (pr2 f)).
    apply proofirrelevance. apply isapropismonoidfun.
  Defined.
End ABGR_preadditive.


(** ** ABGR is Additive
  In the following section we prove that the category of abelian groups is an
  additive category.
 *)
Section ABGR_Additive.

  (** Some lemmas useful to direct sums in the category of abelian groups. *)
  Lemma ABGR_DirectSumPr1 (A B : abgr) : ABGR⟦abgrdirprod A B, A⟧.
  Proof.
    use monoidfunconstr. intros X. exact (pr1 X).
    unfold ismonoidfun. split.
    unfold isbinopfun. intros x x'. unfold op at 1. cbn. apply idpath.
    cbn. apply idpath.
  Defined.

  Lemma ABGR_DirectSumPr2 (A B : abgr) : ABGR⟦abgrdirprod A B, B⟧.
  Proof.
    use monoidfunconstr. intros X. exact (pr2 X).
    unfold ismonoidfun. split.
    unfold isbinopfun. intros x x'. unfold op at 1. cbn. apply idpath.
    cbn. apply idpath.
  Defined.

  Lemma ABGR_DirectSumIn1 (A B : abgr) : ABGR⟦A, abgrdirprod A B⟧.
  Proof.
    use monoidfunconstr. intros a. exact (dirprodpair a (unel B)).
    unfold ismonoidfun. split.
    unfold isbinopfun. intros x x'.
    use dirprodeq. apply idpath. cbn.
    apply pathsinv0. apply (runax B).
    unfold dirprodpair. use total2_paths; apply idpath.
  Defined.

  Lemma ABGR_DirectSumIn2 (A B : abgr) : ABGR⟦B, abgrdirprod A B⟧.
  Proof.
    use monoidfunconstr. intros b. exact (dirprodpair (unel A) b).
    unfold ismonoidfun. split.

    unfold isbinopfun. intros x x'.
    use dirprodeq. cbn. apply pathsinv0. apply (runax A). apply idpath.

    unfold dirprodpair. use total2_paths; apply idpath.
  Defined.

  Lemma ABGR_DirectSumIdIn1 (A B : abgr) :
    ABGR_DirectSumIn1 A B ;; ABGR_DirectSumPr1 A B = idabgrfun A.
  Proof.
    use total2_paths. cbn. use funextfun. intros x. apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumIdIn2 (A B : abgr) :
    ABGR_DirectSumIn2 A B ;; ABGR_DirectSumPr2 A B = idabgrfun B.
  Proof.
    use total2_paths. cbn. use funextfun. intros x. apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumUnel1 (A B : abgr) :
    ABGR_DirectSumIn1 A B ;; ABGR_DirectSumPr2 A B = ABGR_hombinop_unel A B.
  Proof.
    use total2_paths. cbn. use funextfun. intros x. apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumUnel2 (A B : abgr) :
    ABGR_DirectSumIn2 A B ;; ABGR_DirectSumPr1 A B = ABGR_hombinop_unel B A.
  Proof.
    use total2_paths. cbn. use funextfun. intros x. apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumId (A B : abgr) :
    ABGR_hombinop _ _ (ABGR_DirectSumPr1 A B ;; ABGR_DirectSumIn1 A B)
                  (ABGR_DirectSumPr2 A B ;; ABGR_DirectSumIn2 A B)
    = idabgrfun _.
  Proof.
    use total2_paths. cbn. use funextfun. intros x.
    apply dirprodeq. apply (runax A). apply (lunax B).

    apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** A proof that the category of abelian groups is an additive category. *)
  Definition ABGR_Additive : Additive.
  Proof.
    use mk_Additive.
    exact (ABGR_PreAdditive).
    use mk_isAdditive.
    apply ABGR_has_zero.

    intros X Y.
    use BinDirectSums.mk_BinDirectSumCone.
    exact (abgrdirprod X Y).
    exact (ABGR_DirectSumIn1 _ _).
    exact (ABGR_DirectSumIn2 _ _).
    exact (ABGR_DirectSumPr1 _ _).
    exact (ABGR_DirectSumPr2 _ _).

    use BinDirectSums.mk_isBinDirectSumCone.

    (* BinProduct *)
    use (bincoproducts.mk_isBinCoproductCocone _ has_homsets_ABGR).
    intros Z f g.

    use (unique_exists); cbn.

    (* Construction of the morphism from X ⊕ Y to Z. *)
    use monoidfunconstr.
    exact (pr1( ABGR_hombinop _ _ (ABGR_DirectSumPr1 X Y ;; f)
                              (ABGR_DirectSumPr2 X Y ;; g))).
    split.
    intros x x'. cbn. unfold funcomp. cbn.
    rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 g)).
    repeat rewrite <- (assocax (abgrtoabmonoid Z)). apply cancel_rop.
    repeat rewrite (assocax (abgrtoabmonoid Z)). apply cancel_lop.
    apply (pr2 (pr2 Z)).

    cbn. unfold funcomp. cbn.
    set (HH := pr2 (pr2 f)). cbn in HH. rewrite -> HH.
    set (HHg := pr2 (pr2 g)). cbn in HHg. rewrite HHg.
    apply (runax (abgrtoabmonoid Z)).

    (* Commutativity of the morphism. *)
    split.

    use total2_paths. cbn. apply funextfun. intros x.
    unfold funcomp. cbn. set (HHg := pr2 (pr2 g)). cbn in HHg. rewrite HHg.
    apply (runax (abgrtoabmonoid Z)).
    apply proofirrelevance. apply isapropismonoidfun.

    use total2_paths. cbn. apply funextfun. intros x.
    unfold funcomp. cbn. set (HHf := pr2 (pr2 f)). cbn in HHf. rewrite HHf.
    apply (lunax (abgrtoabmonoid Z)).
    apply proofirrelevance. apply isapropismonoidfun.

    (* Equality on equality of homsets *)
    intros y. apply isapropdirprod; apply has_homsets_ABGR.

    (* Uniqueness *)
    intros y z. use total2_paths. cbn. apply funextfun. intros x.
    unfold funcomp. rewrite <- (idabgrfun_remove_left _ _ y).
    rewrite <- (ABGR_DirectSumId X Y). cbn. unfold funcomp.
    rewrite <- (dirprod_pr1 z). rewrite <- (dirprod_pr2 z).
    cbn. unfold funcomp.
    rewrite (runax (abgrtoabmonoid X)). rewrite (lunax (abgrtoabmonoid Y)).
    rewrite <- (pr1 (pr2 y)). cbn.
    rewrite (runax (abgrtoabmonoid X)). rewrite (lunax (abgrtoabmonoid Y)).
    apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.


    (* BinCoproduct *)
    use (binproducts.mk_isBinProductCone _ has_homsets_ABGR).
    intros Z f g.

    use (unique_exists); cbn.

    (* Construction of the morphism from Z to X ⊕ Y. *)
    use monoidfunconstr.
    exact (pr1( ABGR_hombinop _ _ (f ;; ABGR_DirectSumIn1 X Y)
                              (g ;; ABGR_DirectSumIn2 X Y))).
    split.
    intros x x'. cbn. apply dirprodeq.

    cbn. repeat rewrite (runax (abgrtoabmonoid X)).
    rewrite (pr1 (pr2 f)). apply idpath.

    cbn. repeat rewrite (lunax (abgrtoabmonoid Y)).
    rewrite (pr1 (pr2 g)). apply idpath.


    apply dirprodeq.
    cbn. set (HHf := pr2 (pr2 f)). cbn in HHf. rewrite HHf.
    apply (runax (abgrtoabmonoid X)).

    cbn. set (HHg := pr2 (pr2 g)). cbn in HHg. rewrite HHg.
    apply (lunax (abgrtoabmonoid Y)).

    (* Commutativity of the morphism. *)
    split.

    use total2_paths. cbn. apply funextfun. intros x.
    unfold funcomp. cbn. rewrite (runax (abgrtoabmonoid X)). apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    use total2_paths. cbn. apply funextfun. intros x.
    unfold funcomp. cbn. rewrite (lunax (abgrtoabmonoid Y)). apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* Equality on equality of homsets *)
    intros y. apply isapropdirprod; apply has_homsets_ABGR.

    (* Uniqueness *)
    intros y z. use total2_paths. cbn. apply funextfun. intros x.
    rewrite <- (idabgrfun_remove_right _ _ y).
    rewrite <- (ABGR_DirectSumId X Y). cbn.
    rewrite <- (dirprod_pr1 z). rewrite <- (dirprod_pr2 z). cbn.
    apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.

    (* Id1 *)
    use total2_paths. apply funextfun. intros x. cbn. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* Id2 *)
    use total2_paths. apply funextfun. intros x. cbn. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* Unit1 *)
    use total2_paths. apply funextfun. intros x. cbn. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* Unit2 *)
    use total2_paths. apply funextfun. intros x. cbn. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* ID *)
    use total2_paths. apply funextfun. intros x. induction x.
    cbn. apply dirprodeq. cbn. apply (runax (abgrtoabmonoid X)).
    cbn. apply (lunax (abgrtoabmonoid Y)).
    apply proofirrelevance. apply isapropismonoidfun.
  Defined.
End ABGR_Additive.


(** In the following section we construct Kernels and Cokernels in ABGR. *)
Section ABGR_kernels.

  (** hsubtypes for forming the subgroups kernel and image, and also the
      quotient group for cokernel. These are needed to use the relevant results
      in Algebra/Monoid_and_Groups.v . *)
  Definition ABGR_kernel_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtypes A
    := (fun x : A => ishinh ((f x) = unel B)).

  Definition ABGR_image_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtypes B
    := (fun y : B => ∃ x : A, (f x) = y).


  (** An equality we are going to use. *)
  Definition funeqpaths {X Y : UU} {f g: X -> Y} (e : f = g):
    forall (x : X), f x = g x.
  Proof.
    induction e. intros x. apply idpath.
  Qed.


  (*** Kernels *)

  (** Construction of the kernel of f. *)
  Definition ABGR_kernel_subabgr {A B : abgr} (f : monoidfun A B) : @subabgrs A.
  Proof.
    use subgrconstr.
    exact (@ABGR_kernel_hsubtype A B f).
    cbn. split.

    (* issubmonoid *)
    split.

    intros a a'.  induction a as [a1 a2]. induction a' as [a'1 a'2].
    cbn in *. rewrite (pr1 (pr2 f)). unfold ishinh_UU in *.
    intros P X. apply (a2 P). intros a3. apply (a'2 P). intros a'3. apply X.
    cbn in *. rewrite a3. rewrite a'3. apply (runax (abgrtoabmonoid B)).

    intros P X. apply X. cbn in *. rewrite <- (pr2 (pr2 f)).
    apply idpath.

    (* inverse *)
    intros x a.
    unfold ABGR_kernel_hsubtype in *.
    rewrite (monoidfuninvtoinv f x).
    cbn in *.
    unfold ishinh_UU in *. intros P X. apply a. intros X1.
    rewrite -> X1 in X. apply X. apply (grinvunel B).
  Defined.

  (** Construction of the morphism from the kernel of A to A. *)
  Definition ABGR_kernel_monoidfun {A B : abgr} (f : monoidfun A B) :
    ABGR⟦carrierofasubabgr (ABGR_kernel_subabgr f), A⟧.
  Proof.
    use monoidincltomonoidfun.
    use monoidmonopair.
    use inclpair.
    unfold ABGR_kernel_subabgr. cbn. apply pr1carrier. apply isinclpr1carrier.

    (* ismonoidfun *)
    split.
    cbn. intros a a'. cbn. apply idpath.
    cbn. apply idpath.
  Defined.

  (** ABGR Equality for kernels. *)
  Definition ABGR_kernel_eq {A B : abgr} (f : monoidfun A B) :
    (ABGR_kernel_monoidfun f) ;; f =
    (ABGR_kernel_monoidfun f) ;; (ZeroArrow ABGR ABGR_has_zero A B).
  Proof.
    use total2_paths. cbn. apply funextfun. unfold funcomp, pr1carrier.
    intros x. induction x. cbn in *. unfold ishinh_UU in p.
    use (squash_to_prop p). apply (pr2 (pr1 (pr1 B))).
    intros i. apply i.

    apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  (** Construction of the unique arrow to the kernel object. *)
  Definition ABGR_KernelArrowIn {A B C : ABGR} (h : C --> A) (f : A --> B)
             (H : h ;; f = ABGR_zero_arrow C B):
    ABGR⟦C, carrierofasubabgr (ABGR_kernel_subabgr f)⟧.
  Proof.
    use monoidfunconstr.

    apply base_paths in H. cbn in H. unfold funcomp in H.
    intros c.
    cbn. unfold ABGR_kernel_hsubtype. cbn.
    refine (tpair _ (pr1 h c) _). cbn.
    unfold ishinh_UU. intros P X. apply X.
    apply (funeqpaths H c).

    (* ismonoidfun *)
    split.

    intros y y'. cbn. use total2_paths. cbn. rewrite (pr1 (pr2 h)).
    apply idpath.
    apply proofirrelevance. cbn. apply isapropishinh.

    use total2_paths. cbn. apply (pr2 (pr2 h)).
    apply proofirrelevance. cbn. apply isapropishinh.
  Defined.

  (** Construction of a kernel of a morphism of abelian groups f. *)
  Definition ABGR_kernel {A B : abgr} (f : monoidfun A B) :
    Kernel ABGR_has_zero f.
  Proof.
    induction A. induction B.
    use mk_Kernel.
    exact (carrierofasubabgr (ABGR_kernel_subabgr f)).
    exact (ABGR_kernel_monoidfun f).
    rewrite (ABGR_kernel_eq f).
    apply (ZeroArrow_comp_right ABGR ABGR_has_zero).

    use mk_isEqualizer.
    intros w h H'. induction w. induction h.
    use unique_exists.

    (* Construction of the unique arrow into kernel *)
    rewrite (ZeroArrow_comp_right ABGR ABGR_has_zero _ _) in H'.
    rewrite (ABGR_has_zero_arrow_eq _ _) in H'.
    apply (ABGR_KernelArrowIn _ f H').

    (* Commutativity of the kernel arrow *)
    use total2_paths. apply funextfun. intros x. cbn. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* Equality of equalities of morphisms *)
    intros y. apply has_homsets_ABGR.

    (* Uniqueness *)
    intros y t3. induction y. apply base_paths in t3. cbn in *.
    unfold pr1carrier, funcomp in t3. cbn in t3. use total2_paths.
    cbn. apply funextfun. intros x.
    use total2_paths. cbn. exact (funeqpaths t3 x).

    apply proofirrelevance. apply isapropishinh.
    apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  (** As a corollary we get that ABGR has kernels. *)
  Corollary ABGR_kernels : Kernels ABGR_has_zero.
  Proof.
    intros A B f. apply (ABGR_kernel f).
  Defined.


  (*** Cokernels *)

  (** Construction of the image of f. *)
  Definition ABGR_image {A B : abgr} (f : monoidfun A B) : @subabgrs B.
  Proof.
    unfold subabgrs.
    use subgrconstr.
    exact (@ABGR_image_hsubtype A B f).
    cbn. split.

    (* issubmonoid *)
    split.

    intros a a'.  induction a as [a1 a2]. induction a' as [a'1 a'2].
    cbn in *.  unfold ishinh_UU in *.
    intros P X. apply (a2 P). intros a3. apply (a'2 P). intros a'3. apply X.
    cbn in *. use tpair.  induction a3. induction a'3.
    apply (op t t0). cbn. unfold total2_rect.
    induction a3. induction a'3. rewrite (pr1 (pr2 f)). cbn in *.
    rewrite p. rewrite p0. apply idpath.

    intros P X. apply X. use tpair. exact (unel A). cbn.
    rewrite <- (pr2 (pr2 f)). apply idpath.

    (* inverse *)
    intros x a.
    unfold ABGR_image_hsubtype in *. unfold ishinh in *. cbn in *.
    unfold ishinh_UU in *. intros P X. apply a. intros X1. apply X.
    induction X1. use tpair. apply (grinv A t). cbn.
    set (XXt := monoidfuninvtoinv f t). cbn in XXt.
    rewrite XXt. rewrite p. apply idpath.
  Defined.

  (** The eqrel on B used to form the quotient group of the cokernel of f. *)
  Definition ABGR_cokernel_eqrel {A B : abgr} (f : monoidfun A B) : eqrel B.
  Proof.
    use eqrelconstr.

    (* The relation *)
    exact (fun b1 : B => fun b2 : B => ∃ a : A, (f a) = (op b1 (grinv B b2))).

    (* Transitivity *)
    intros x1 x2 x3 y1 y2.
    unfold ishinh in *. cbn in *. unfold ishinh_UU in *. intros P X.
    apply y1. intros Y1. apply y2. intros Y2. induction Y1, Y2. apply X.
    refine (tpair _ (op t t0) _). rewrite (pr1 (pr2 f)). cbn in *.
    rewrite p. rewrite p0.

    rewrite <- (assocax (abgrtoabmonoid B)).
    rewrite (assocax (abgrtoabmonoid B) x1 _ _).
    rewrite (grlinvax B). rewrite (runax B).
    apply idpath.

    (* Reflexivity *)
    intros x1 y1 y2. apply y2. refine (tpair _ (unel A) _).
    rewrite (grrinvax B). rewrite <- (pr2 (pr2 f)). apply idpath.

    (* Symmetry *)
    intros x1 x2 x3 y1 y2.
    unfold ishinh in *. cbn in *. unfold ishinh_UU in *. apply x3.
    intros X3. apply y2. induction X3. refine (tpair _ (grinv A t) _).
    set (XXf := (grinvandmonoidfun A B (pr2 f) t)). cbn in XXf.
    rewrite XXf. rewrite p.
    set (XXB := grinvcomp B x1 (grinv B x2)). cbn in XXB.
    rewrite XXB. rewrite grinvinv. apply idpath.
  Defined.

  (** Construction of the cokernel of f. We need to take the quotient group of
    B by the image of f. *)
  Definition ABGR_cokernel_abgr {A B : abgr} (f : monoidfun A B) : abgr.
  Proof.
    use (@abgrquot B).
    use binopeqrelpair.

    exact (ABGR_cokernel_eqrel f).

    (* isbinoprel *)
    cbn. use isbinophrelif. apply (pr2 (pr2 B)).
    intros x1 x2 x3 y1. cbn in *. unfold ishinh_UU in *. intros P X.
    apply y1. intros Y1. induction Y1. apply X.
    refine (tpair _ t _). rewrite p. rewrite ((pr2 (pr2 B)) x3 _).
    rewrite (assocax B). apply cancel_lop. rewrite ((pr2 (pr2 B)) x3 _).
    rewrite grinvcomp. rewrite (assocax B). rewrite (grlinvax B).
    rewrite (runax B). apply idpath.
  Defined.

  (** Construction of the monoidfun from B to the cokernel of f. *)
  Definition ABGR_cokernel_monoidfun {A B : abgr} (f : monoidfun A B) :
    ABGR⟦B, ABGR_cokernel_abgr f⟧.
  Proof.
    use monoidfunconstr.
    use (setquotpr (ABGR_cokernel_eqrel f)).

    (* ismonoidfun *)
    split. split. apply idpath.
  Defined.

  (** ABGR Equality for cokernels. *)
  Definition ABGR_cokernel_eq' {A B : abgr} (f : ABGR⟦A, B⟧) :
    f ;; (ABGR_cokernel_monoidfun f) = ABGR_zero_arrow A (ABGR_cokernel_abgr f).
  Proof.
    use total2_paths. apply funextfun. intros a.
    apply (iscompsetquotpr (ABGR_cokernel_eqrel f)).
    unfold ABGR_cokernel_eqrel.
    intros P X. cbn in *. apply X. refine (tpair _ a _).
    use (pathscomp0 (pathsinv0 (runax B (pr1 f a)))).
    apply cancel_lop.
    use (pathscomp0 (pathsinv0 (grinvunel B))).
    apply maponpaths. apply idpath.

    apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  (** ABGR Equality for cokernels. *)
  Definition ABGR_cokernel_eq {A B : abgr} (f : ABGR⟦A, B⟧) :
      f ;; (ABGR_cokernel_monoidfun f) =
      (ZeroArrow ABGR ABGR_has_zero A B) ;; (ABGR_cokernel_monoidfun f).
  Proof.
    rewrite ZeroArrow_comp_left.
    rewrite ABGR_has_zero_arrow_eq.
    exact (ABGR_cokernel_eq' f).
  Defined.

  (** The following result is used to show that map from setquot is a
    monoidfun. *)
  Definition isbinopfun_2of3 {A B C : setwithbinop} (f : (pr1 A) -> (pr1 B))
             (g : (pr1 B) -> (pr1 C)) (H : issurjective f):
    isbinopfun (g ∘ f) -> isbinopfun f -> isbinopfun g.
  Proof.
    intros h f'.
    intros b1 b2.
    unfold issurjective in H. cbn in H.
    set (H1 := H b1).
    set (H2 := H b2).
    use (squash_to_prop H1). apply (pr2 (pr1 C)).
    intros HH1.
    use (squash_to_prop H2). apply (pr2 (pr1 C)).
    intros HH2.
    unfold hfiber in *. induction HH1. induction HH2.
    rewrite <- p. rewrite <- p0. rewrite <- f'. cbn.

    assert (g (f (t * t0)%multmonoid) = (g ∘ f) (t * t0)%multmonoid).
    unfold funcomp. apply idpath. cbn in X. rewrite X.

    rewrite h. unfold funcomp. apply idpath.
  Defined.

  (** Construction of the unique arrow out of the cokernel. *)
  Definition ABGR_CokernelArrowOutUniv {A B C : ABGR} (f : A --> B) (h : B --> C)
             (H : (λ x : pr1 A, (pr1 h) (pr1 f x))
                  = (λ _ : pr1 A, 1%multmonoid)):
    (ABGR_cokernel_abgr f) -> (pr1 C).
  Proof.
    cbn. use setquotuniv. apply (pr1 h).
    unfold iscomprelfun. intros x x' X.
    use (squash_to_prop X). apply (pr2 (pr1 (pr1 C))).
    intros X'. induction X'.
    set (Y := funeqpaths H t). cbn in Y.
    apply (maponpaths (pr1 h)) in p. cbn in *.
    rewrite Y in p. rewrite (pr1 (pr2 h)) in p.
    apply (grrcan (abgrtogr C) ((pr1 h) (grinv (abgrtogr B) x'))).
    cbn in *.
    rewrite <- p. rewrite <- (pr1 (pr2 h)). apply pathsinv0.
    rewrite (grrinvax (abgrtogr B) x'). apply (pr2 (pr2 h)).
  Defined.

  (** Construction of a cokernel of a morphism of abelian groups f. *)
  Definition ABGR_cokernel {A B : abgr} (f : monoidfun A B) :
    Cokernel ABGR_has_zero f.
  Proof.
    use mk_Cokernel.
    exact (ABGR_cokernel_abgr f).
    exact (ABGR_cokernel_monoidfun f).
    rewrite (ABGR_cokernel_eq f).
    apply (ZeroArrow_comp_left ABGR ABGR_has_zero).

    use mk_isCoequalizer.
    intros w h H'.
    use unique_exists.

    (* Construction of the unique arrow out of cokernel *)
    use monoidfunconstr.
    rewrite (ZeroArrow_comp_left ABGR ABGR_has_zero _ _) in H'.
    rewrite (ABGR_has_zero_arrow_eq _ _) in H'.
    apply base_paths in H'. cbn in H'. unfold funcomp in H'.
    apply (ABGR_CokernelArrowOutUniv f _ H').

    (* ismonoidfun *)
    split.

    use isbinopfun_2of3. apply (pr1 B). apply (pr1 (ABGR_cokernel_monoidfun f)).
    apply issurjsetquotpr. unfold funcomp.
    apply (pr2 h). apply (pr2 (ABGR_cokernel_monoidfun f)).

    cbn. set (XXh := pr2 (pr2 h)). cbn in XXh. rewrite <- XXh.
    apply maponpaths. apply idpath.

    (* Commutativity *)
    induction h.
    use total2_paths. cbn. apply funextfun. intros b. apply idpath.
    apply proofirrelevance. apply isapropismonoidfun.

    (* Equality on equality of morphisms *)
    intros y. cbn. intros x x'. apply (has_homsets_ABGR).

    (* Uniqueness *)
    intros y. induction y. intros  t0. cbn in t0.
    use total2_paths. cbn. apply funextfun.
    intros z. cbn in *.
    set (surj := issurjsetquotpr (ABGR_cokernel_eqrel f)).
    unfold issurjective in surj. cbn in surj.
    set (surjz := surj z).
    use (squash_to_prop surjz). apply (pr2 (pr1 (pr1 w))).
    intros surjz'. unfold hfiber in surjz'. induction surjz'.
    rewrite <- p0. cbn. apply base_paths in t0. cbn in t0.
    unfold funcomp in t0. apply (funeqpaths t0 t1).

    apply proofirrelevance. apply isapropismonoidfun.
  Defined.

  (** As a corollary we get that ABGR has cokernels. *)
  Corollary ABGR_cokernels : Cokernels ABGR_has_zero.
  Proof.
    intros A B f. apply (ABGR_cokernel f).
  Defined.
End ABGR_kernels.
