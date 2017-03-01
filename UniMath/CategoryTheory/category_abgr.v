(** * Category of abelian groups *)
(** ** Contents
- Definition of the category of abelian groups, ABGR
- Iso and monoidiso are weakly equivalent
- General results (TODO: find a place for these )
- Zero object and Zero arrow
 - Zero object
 - Zero arrow
- ABGR is PreAdditive
- ABGR is Additive
- Kernels and Cokernels
 - Kernels
 - Cokernels
- Monics are inclusions and Epis are surjections
 - Preliminaries
 - Epis are surjections
 - Monics are inclusions
- Monics are Kernels and Epis are Cokernels
 - Monics are Kernels
 - Epis are Cokernels
- ABGR is AbelianPreCat
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.precategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.


(** * Definition of the category of abelian groups
  In this section we define the category of abelian groups. *)
Section ABGR_precategory.

  (** Objects are abgr and morphisms are monoidfun. *)
  Definition abgr_fun_space (A B : abgr) : hSet := hSetpair _ (isasetmonoidfun A B).

  Definition abgr_precategory_ob_mor : precategory_ob_mor :=
    tpair (fun ob : UU => ob -> ob -> UU) abgr (fun A B : abgr => abgr_fun_space A B).

  Definition idabgrfun_ismonoidfun (A : abgr) : ismonoidfun (fun a : A => a).
  Proof.
    split.
    - intros a a'. apply idpath.
    - apply idpath.
  Qed.

  (** Identity morphism. *)
  Definition idabgrfun (A : abgr) : monoidfun A A := monoidfunconstr (idabgrfun_ismonoidfun A).

  Definition idabgrfun_left (A B : abgr) (f : monoidfun A B) : monoidfuncomp (idabgrfun A) f = f.
  Proof.
    unfold monoidfuncomp. unfold idabgrfun.
    use total2_paths_f.
    - cbn. unfold funcomp. apply maponpaths. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Definition idabgrfun_right (A B : abgr) (f : monoidfun A B) : monoidfuncomp f (idabgrfun B) = f.
  Proof.
    unfold monoidfuncomp, idabgrfun.
    use total2_paths_f.
    - cbn. unfold funcomp. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Associativity. *)
  Definition abmonoidfuncomp_assoc (A B C D : abmonoid) (f : monoidfun A B) (g : monoidfun B C)
             (h : monoidfun C D) :
    monoidfuncomp (monoidfuncomp f g) h = monoidfuncomp f (monoidfuncomp g h).
  Proof.
    use total2_paths_f.
    - cbn. unfold funcomp. apply funextfun. intros x. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Definition abgrfuncomp_assoc (A B C D : abgr) (f : monoidfun A B) (g : monoidfun B C)
             (h : monoidfun C D) :
    monoidfuncomp (monoidfuncomp f g) h = monoidfuncomp f (monoidfuncomp g h).
  Proof.
    apply (abmonoidfuncomp_assoc A B C D f g h).
  Qed.

  (** Construction of the precategory ABGR. *)
  Definition abgr_precategory_data : precategory_data :=
    precategory_data_pair
      abgr_precategory_ob_mor (fun (A : abgr) => idabgrfun A )
      (fun (A B C : abgr) (f : monoidfun A B) (g : monoidfun B C) => monoidfuncomp f g).

  Lemma is_precategory_abgr_precategory_data : is_precategory abgr_precategory_data.
  Proof.
    repeat split; cbn.
    - intros a b f. apply idabgrfun_left.
    - intros a b f. apply idabgrfun_right.
    - intros a b c d f g h. apply pathsinv0.
      apply (abgrfuncomp_assoc a b c d f g h).
  Qed.

  Definition abgr_precategory : precategory := tpair _ _ is_precategory_abgr_precategory_data.

  Lemma has_homsets_ABGR : has_homsets abgr_precategory.
  Proof.
    intros a b. apply isasetmonoidfun.
  Qed.

End ABGR_precategory.


(** Denote this category by ABGR. *)
Notation ABGR := abgr_precategory.


(** * In [ABGR], iso ≃ monoidiso
    In this section we construct a weak equivalence between isomorphisms in ABGR and monoidisos. *)
Section ABGR_category.

  Lemma abgr_iso_is_equiv (A B : ob ABGR) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Qed.

  Lemma abgrp_iso_equiv (A B : ob ABGR) :
    iso A B -> monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B).
  Proof.
    intro f.
    use monoidisopair.
    - set (X := abgr_iso_is_equiv A B f).
      apply (weqpair (pr1 (pr1 f)) X).
    - apply (pr2 (pr1 f)).
  Defined.

  Lemma abgr_equiv_is_iso (A B : abgr) (f : monoidiso A B) :
    @is_isomorphism ABGR A B (monoidfunconstr (pr2 f)).
  Proof.
    apply (is_iso_qinv (C:=ABGR) _ (monoidfunconstr (pr2 (invmonoidiso f)))).
    split; cbn.
    - unfold monoidfuncomp, compose, idabgrfun, identity.
      use total2_paths_f.
      + cbn. apply funextfun. intros x.
        apply homotinvweqweq.
      + cbn. use total2_paths_f.
        * apply proofirrelevance. apply isapropisbinopfun.
        * apply proofirrelevance. exact (setproperty _ _ _).
    - use total2_paths_f.
      + apply funextfun. intros x. apply homotweqinvweq.
      + apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma abgr_equiv_iso (A B : ABGR) : monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B) -> iso A B.
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
    - intro; apply eq_iso. apply maponpaths.
      unfold abgr_equiv_iso, abgrp_iso_equiv. cbn.
      use total2_paths_f.
      + cbn. unfold monoidfunconstr.
        apply subtypeEquality. intros y. apply isapropismonoidfun.
        apply maponpaths. apply subtypeEquality.
        * unfold isPredicate. intros x0. apply isapropismonoidfun.
        * apply idpath.
      + apply proofirrelevance. apply isaprop_is_iso.
    - intros y. unfold abgrp_iso_equiv, abgr_equiv_iso. cbn.
      use total2_paths_f.
      + unfold monoidfunconstr. apply subtypeEquality.
        intros x. apply isapropisweq. apply idpath.
      + apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Definition abgr_iso_equiv_weq (A B : ABGR) :
    weq (iso A B) (monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B)).
  Proof.
    exists (abgrp_iso_equiv A B).
    apply abgrp_iso_equiv_is_equiv.
  Qed.

  Lemma abgr_equiv_iso_is_equiv (A B : ABGR) : isweq (abgr_equiv_iso A B).
  Proof.
    apply (gradth _ (abgrp_iso_equiv A B)).
    - intros x. apply subtypeEquality.
      + intros y. apply isapropismonoidfun.
      + unfold abgr_equiv_iso, abgrp_iso_equiv. cbn.
        use total2_paths_f.
        * apply idpath.
        * apply isapropisweq.
    - intros y. unfold abgr_equiv_iso, abgrp_iso_equiv. cbn.
      use total2_paths_f.
      + unfold monoidfunconstr. cbn. apply subtypeEquality.
        * intros x. apply isapropismonoidfun.
        * apply idpath.
      + apply proofirrelevance. apply isaprop_is_iso.
  Qed.

  Definition hbinop_equiv_iso_weq (A B : ABGR) :
    weq (monoidiso (abgrtoabmonoid A) (abgrtoabmonoid B)) (iso A B).
  Proof.
    exists (abgr_equiv_iso A B).
    apply abgr_equiv_iso_is_equiv.
  Qed.


(** ** HERE ONE SHOULD ADD A PROOF THAT ABGR IS ACTUALLY A CATEGORY.
         See category_hset.v *)

End ABGR_category.


(** ** General results
  Move these *)
Section ABGR_general.

  Definition monoidfun_eq {A B : abgr} (f g : monoidfun A B) (H : ∏ (x : A), f x = g x) : f = g.
  Proof.
    use total2_paths_f.
    - use funextfun. intros x. exact (H x).
    - use proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Binop preserves equality. *)
  Lemma lopeq (X : setwithbinop) (x y z : X) : x = y -> @op X z x = @op X z y.
  Proof.
    intros e. apply maponpaths. exact e.
  Qed.

  Lemma ropeq (X : setwithbinop) (x y z : X) : x = y -> @op X x z = @op X y z.
  Proof.
    intros e. induction e. apply idpath.
  Qed.

  (** Monoidfun preserves inverses. *)
  Definition monoidfun_inv {A B : abgr} (f : monoidfun A B) (a : A) : f (grinv A a) = grinv B (f a).
  Proof.
    apply (grlcan B (f a)). rewrite (grrinvax B).
    use (pathscomp0 (pathsinv0 (((pr1 (pr2 f)) a (grinv A a))))).
    rewrite (grrinvax A). apply (pr2 (pr2 f)).
  Qed.

  (** Multiplication of hfibers. *)
  Definition hfiber_op_eq {A B : abgr} (f : monoidfun A B) (b1 b2 : B) (hf1 : hfiber (pr1 f) b1)
             (hf2 : hfiber (pr1 f) b2) :
    pr1 f (pr1 hf1 * pr1 hf2)%multmonoid = (b1 * b2)%multmonoid.
  Proof.
    rewrite (pr1 (pr2 f)).
    rewrite (pr2 hf1).
    rewrite (pr2 hf2).
    apply idpath.
  Qed.

  Definition hfiber_op {A B : abgr} (f : monoidfun A B) (b1 b2 : B) (hf1 : hfiber (pr1 f) b1)
             (hf2 : hfiber (pr1 f) b2) : hfiber (pr1 f) (b1 * b2)%multmonoid :=
    hfiberpair (pr1 f) ((pr1 hf1) * (pr1 hf2))%multmonoid (hfiber_op_eq f b1 b2 hf1 hf2).

  (** hsubtype for forming the subgroups kernel and image, and also the quotient group for
      cokernel. These are needed to use the relevant results in Algebra/Monoid_and_Groups.v. *)
  Definition ABGR_kernel_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtype A :=
    (fun x : A => ishinh ((f x) = unel B)).

  Definition ABGR_image_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtype B :=
    (fun y : B => ∃ x : A, (f x) = y).

  (** An equality we are going to use. *)
  Definition funeqpaths {X Y : UU} {f g: X -> Y} (e : f = g) : ∏ (x : X), f x = g x.
  Proof.
    induction e. intros x. apply idpath.
  Qed.

End ABGR_general.


(** * Zero object and Zero arrow
    In the following section we prove that the category of abelian groups has a zero object. *)
Section ABGR_zero.

  (** Hide isabgrop behind Qed. *)
  Definition ABGR_zero_isabgrop : isabgrop (pr2 (setwithbinoppair unitset (λ i _ : unitset, i))).
  Proof.
    unfold isabgrop. split.
    - use isgroppair.
      + split.
        * unfold isassoc. intros x x' x''.
          unfold op. cbn. apply idpath.
        * use isunitalpair.
          -- cbn. exact tt.
          -- unfold isunit. split.
             ++ unfold islunit. intros x. cbn. apply isconnectedunit.
             ++ unfold isrunit. intros x. cbn. apply isconnectedunit.
      + unfold invstruct. cbn. use (tpair _ (fun _ : unit => tt)).
        cbn. unfold isinv. split.
        * unfold islinv. intros X. apply idpath.
        * unfold isrinv. intros x. apply isconnectedunit.
    - unfold iscomm. intros x x'. unfold op. cbn.  apply isconnectedunit.
  Qed.

  (** The zero object we use consists of one element, the unit element. *)
  Definition ABGR_zero : abgr := abgrpair (setwithbinoppair unitset (fun i i': unitset => i))
                                          (ABGR_zero_isabgrop).

  (** The zero object is connected. *)
  Lemma ABGR_zero_connected : ∏ x x' : ABGR_zero, x = x'.
  Proof.
    unfold ABGR_zero. cbn. intros x x'.
    apply isconnectedunit.
  Qed.

  (** Hide ismonoid behind Qed. *)
  Definition ABGR_zero_from_ismonoid (A : abgr) :
    @ismonoidfun A ABGR_zero (fun a : A => (unel ABGR_zero)).
  Proof.
    unfold ismonoidfun. unfold isbinopfun. cbn. split.
    intros x x'. apply idpath.
    apply idpath.
  Qed.

  (** Construction of the morphism to the zero object. *)
  Definition ABGR_zero_from (A : abgr) : ABGR⟦A, ABGR_zero⟧ :=
    monoidfunconstr (ABGR_zero_from_ismonoid A).

  (** Hide ismonoid behind Qed. *)
  Definition ABGR_zero_to_ismonoid (A : abgr) : @ismonoidfun ABGR_zero A (fun a : _ => (unel A)).
  Proof.
    unfold ismonoidfun. unfold isbinopfun. cbn. split.
    intros x x'. rewrite (runax A). apply idpath.
    apply idpath.
  Qed.

  (** Construction of the morphisms from the zero object. *)
  Definition ABGR_zero_to (A : abgr) : ABGR⟦ABGR_zero, A⟧ :=
    monoidfunconstr (ABGR_zero_to_ismonoid A).

  Definition ABGR_zero_arrow_ismonoid (A B : abgr) : @ismonoidfun A B (fun a : _ => (unel B)).
  Proof.
    unfold ismonoidfun. unfold isbinopfun. cbn. split.
    intros x x'. rewrite (runax B). apply idpath.
    apply idpath.
  Qed.

  (** Construction of the zero arrow between two arbitrary objects. *)
  Definition ABGR_zero_arrow (A B : abgr) : ABGR⟦A, B⟧ :=
    monoidfunconstr (ABGR_zero_arrow_ismonoid A B).

  (** Hide isZero behind Qed. *)
  Definition ABGR_has_zero_iszero : isZero ABGR ABGR_zero.
  Proof.
    use mk_isZero.
    - intros a. use iscontrpair.
      + exact (ABGR_zero_to a).
      + intros t. use total2_paths_f.
        * apply funextfun. intros x.
          unfold ABGR_zero_to. cbn.
          rewrite (isconnectedunit x (unel ABGR_zero)). apply (pr2 (pr2 t)).
        * apply proofirrelevance. apply isapropismonoidfun.
    - intros a. use iscontrpair.
      + exact (ABGR_zero_from a).
      + intros t. use total2_paths_f.
        * apply funextfun. intros x. apply isconnectedunit.
        * apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** The following lemma constructs a zero object in ABGR. *)
  Definition ABGR_has_zero : Zero ABGR := @mk_Zero ABGR ABGR_zero ABGR_has_zero_iszero.

  (** The following lemmas verify that the above definition behaves as
    expected. *)
  Lemma ABGR_has_zero_ob : ZeroObject (ABGR_has_zero) = ABGR_zero.
  Proof.
    apply idpath.
  Qed.

  Lemma ABGR_has_zero_from (A : abgr) : @ZeroArrowFrom ABGR ABGR_has_zero A = ABGR_zero_to A.
  Proof.
    apply ArrowsFromZero.
  Qed.

  Lemma ABGR_has_zero_to (A : abgr) : @ZeroArrowTo ABGR ABGR_has_zero A = ABGR_zero_from A.
  Proof.
    apply ArrowsToZero.
  Qed.

  Lemma ABGR_has_zero_arrow_eq (A B : abgr) :
    @ZeroArrow ABGR ABGR_has_zero A B = ABGR_zero_arrow A B.
  Proof.
    unfold ZeroArrow.
    rewrite ABGR_has_zero_from.
    rewrite ABGR_has_zero_to.
    use total2_paths_f.
    - cbn. unfold funcomp. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

End ABGR_zero.


(** * ABGR is PreAdditive
    In the following section we prove that ABGR is preadditive. *)
Section ABGR_preadditive.

  (** Hide ismonoidfun behind Qed. *)
  Definition ABGR_hombinop_ismonoidfun {X Y : ABGR} (f g : ABGR⟦X, Y⟧) :
    @ismonoidfun (abgrtoabmonoid X) (abgrtoabmonoid Y)
                 (fun x : pr1 X => (pr1 f x * pr1 g x)%multmonoid).
  Proof.
    split.
    - intros x x'.
      rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 g)).
      repeat rewrite <- (assocax (abgrtoabmonoid Y)). apply ropeq.
      repeat rewrite (assocax (abgrtoabmonoid Y)). apply lopeq.
      rewrite (commax (abgrtoabmonoid Y)). apply idpath.
    - set (tmp := pr2 (pr2 f)). cbn in tmp.  use (pathscomp0 _ tmp).
      set (tmp1 := pr2 (pr2 g)). cbn in tmp1.
      apply (maponpaths (fun h : _ => ((pr1 f 1%multmonoid) * h)%multmonoid)) in tmp1.
      use (pathscomp0 tmp1).
      apply (runax (abgrtoabmonoid Y)).
  Qed.

  (** The binop structure on the category of abelian groups. *)
  Definition ABGR_hombinop (X Y : ABGR) :  ABGR⟦X, Y⟧ -> ABGR⟦X, Y⟧ -> ABGR⟦X, Y⟧.
  Proof.
    intros f g.
    exact (monoidfunconstr (ABGR_hombinop_ismonoidfun f g)).
  Defined.

  (** Verification of the unit axioms for the above binop. *)
  Definition ABGR_hombinop_runax (X Y : ABGR) (f : ABGR⟦X, Y⟧) :
    ABGR_hombinop X Y f (ABGR_zero_arrow X Y) = f.
  Proof.
    use total2_paths_f.
    - cbn. apply funextfun. intros x.
      rewrite (runax (abgrtoabmonoid Y)). apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Definition ABGR_hombinop_lunax (X Y : ABGR) (f : ABGR⟦X, Y⟧) :
    ABGR_hombinop X Y (ABGR_zero_arrow X Y) f = f.
  Proof.
    use total2_paths_f.
    - cbn. apply funextfun. intros x.
      rewrite (lunax (abgrtoabmonoid Y)). apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Commutativity of the binary operation. *)
  Definition ABGR_hombinop_comm (X Y : ABGR) :
    ∏ (f g : ABGR⟦X, Y⟧), @ABGR_hombinop X Y f g = @ABGR_hombinop X Y g f.
  Proof.
    intros f g. use total2_paths_f.
    - cbn. apply funextfun. intros x. rewrite (pr2 (pr2 Y)). apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Definition ABGR_hombinop_inv_ismonoidfun {X Y : ABGR} (f : ABGR⟦X, Y⟧) :
    ismonoidfun (fun x : (abgrtoabmonoid X) => grinv (abgrtogr Y) (pr1 f x)).
  Proof.
    split.
    - intros x x'.
      rewrite (pr1 (pr2 f)). rewrite (pr2 (pr2 Y)).
      rewrite (grinvop (abgrtogr Y)).
      apply idpath.
    - set (tmp := pr2 (pr2 f)). cbn in tmp.
      apply (maponpaths (fun h : _ => grinv (abgrtogr Y) h)) in tmp.
      use (pathscomp0 tmp).
      apply (grinvunel (abgrtogr Y)).
  Qed.

  (** Construction of the inverse function in the category of abelian groups. *)
  Definition ABGR_hombinop_inv (X Y : ABGR) : ABGR⟦X, Y⟧ -> ABGR⟦X, Y⟧.
  Proof.
    intros f.
    exact (monoidfunconstr (ABGR_hombinop_inv_ismonoidfun f)).
  Defined.

  (** Verification that this gives left and right inverse. *)
  Definition ABGR_hombinop_linvax (X Y : ABGR) :
    ∏ f : ABGR⟦X, Y⟧, ABGR_hombinop X Y (ABGR_hombinop_inv X Y f) f  = ABGR_zero_arrow X Y.
  Proof.
    intros f. use total2_paths_f.
    - cbn. apply funextfun. intros x. apply (grlinvax (abgrtogr Y)).
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Definition ABGR_hombinop_rinvax (X Y : ABGR) :
    ∏ f : ABGR⟦X, Y⟧, ABGR_hombinop X Y f (ABGR_hombinop_inv X Y f) = ABGR_zero_arrow X Y.
  Proof.
    intros f. use total2_paths_f.
    - cbn. apply funextfun. intros x. apply (grrinvax (abgrtogr Y)).
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Associativity of the binary operation. *)
  Definition ABGR_hombinop_assoc (X Y : ABGR) (f g h : ABGR⟦X, Y⟧) :
    ABGR_hombinop X Y f (ABGR_hombinop X Y g h) = ABGR_hombinop X Y (ABGR_hombinop X Y f g) h.
  Proof.
    use total2_paths_f.
    - cbn. apply funextfun. intros x. rewrite (assocax (abgrtoabmonoid Y)). apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** ABGR is precategoryWithBinOps. *)
  Definition ABGR_WithBinOpsData : precategoryWithBinOpsData ABGR.
  Proof.
    intros X Y.
    exact (ABGR_hombinop X Y).
  Defined.

  Definition ABGR_WithBinOps : precategoryWithBinOps := tpair _ ABGR ABGR_WithBinOpsData.

  (** ABGR is PrecategoryWithAbgrops. *)
  Definition ABGR_WithAbGrops : PrecategoryWithAbgrops.
  Proof.
    use (mk_PrecategoryWithAbgrops ABGR_WithBinOps has_homsets_ABGR).
    intros X Y.
    split.
    - use isgroppair.
      + split.
        (* Associativity *)
        * intros x y z.
          apply pathsinv0. apply ABGR_hombinop_assoc.
        (* Unit *)
        * use isunitalpair.
          apply ABGR_zero_arrow.
          split.
          -- unfold islunit. intros x. apply (ABGR_hombinop_lunax X Y).
          -- unfold isrunit. intros x. apply (ABGR_hombinop_runax X Y).
      (* invstruct *)
      + use tpair.
        * exact (ABGR_hombinop_inv X Y).
        * split.
          -- intros f. apply ABGR_hombinop_linvax.
          -- intros f. apply ABGR_hombinop_rinvax.
    (* Commutativity *)
    - intros f g. apply (ABGR_hombinop_comm X Y f g).
  Defined.

  (** Hide isPreAdditive behind Qed. *)
  Definition ABGR_isPreAdditive : isPreAdditive ABGR_WithAbGrops.
  Proof.
    use mk_isPreAdditive.
    (* First bilinearity. *)
    - intros X Y Z f.
      split.
      + intros g h.
        unfold to_premor.
        use total2_paths_f.
        * cbn. apply funextfun.
          intros x. unfold funcomp. apply idpath.
        * apply proofirrelevance. apply isapropismonoidfun.
      + unfold to_premor.
        use total2_paths_f.
        * cbn. apply funextfun.
          intros x. unfold funcomp. apply idpath.
        * apply proofirrelevance. apply isapropismonoidfun.
    (* Second bilinearity. *)
    - intros X Y Z f.
      split.
      + intros g h.
        unfold to_premor.
        use total2_paths_f.
        * cbn. apply funextfun.
          intros x. unfold funcomp. rewrite (pr1 (pr2 f)). apply idpath.
        * apply proofirrelevance. apply isapropismonoidfun.
      + unfold to_premor.
        use total2_paths_f.
        * cbn. apply funextfun.
          intros x. unfold funcomp. apply (pr2 (pr2 f)).
        * apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Finally, we prove that the category of abelian groups is preadditive. *)
  Definition ABGR_PreAdditive : PreAdditive := mk_PreAdditive ABGR_WithAbGrops ABGR_isPreAdditive.

End ABGR_preadditive.


(** * ABGR is Additive
  In the following section we prove that the category of abelian groups is an additive category. *)
Section ABGR_Additive.

  (** Verification of the properties of DirectSums. *)
  Lemma ABGR_DirectSumPr1_ismonoidfun (A B : abgr) :
    ismonoidfun (fun X : abgrdirprod A B => dirprod_pr1 X).
  Proof.
    split.
    intros x x'. unfold op at 1. unfold dirprod_pr1. apply idpath.
    apply idpath.
  Qed.

  Definition ABGR_DirectSumPr1 (A B : abgr) : ABGR⟦abgrdirprod A B, A⟧ :=
    monoidfunconstr (ABGR_DirectSumPr1_ismonoidfun A B).

  Lemma ABGR_DirectSumPr2_ismonoidfun (A B : abgr) :
    ismonoidfun (fun X : abgrdirprod A B => dirprod_pr2 X).
  Proof.
    split.
    - intros x x'. unfold op at 1. unfold dirprod_pr2. apply idpath.
    - apply idpath.
  Qed.

  Definition ABGR_DirectSumPr2 (A B : abgr) : ABGR⟦abgrdirprod A B, B⟧ :=
    monoidfunconstr (ABGR_DirectSumPr2_ismonoidfun A B).

  Lemma ABGR_DirectSumIn1_ismonoidfun (A B : abgr) :
    @ismonoidfun A (abgrdirprod A B) (fun a : A => dirprodpair a (unel B)).
  Proof.
    split.
    - intros x x'. use dirprodeq.
      + apply idpath.
      + apply pathsinv0. apply (runax B).
    - unfold dirprodpair. use total2_paths_f; apply idpath.
  Qed.

  Definition ABGR_DirectSumIn1 (A B : abgr) : ABGR⟦A, abgrdirprod A B⟧ :=
    monoidfunconstr (ABGR_DirectSumIn1_ismonoidfun A B).

  Lemma ABGR_DirectSumIn2_ismonoidfun (A B : abgr) :
    @ismonoidfun B (abgrdirprod A B) (fun b : B => dirprodpair (unel A) b).
  Proof.
    split.
    - intros x x'. use dirprodeq.
      + apply pathsinv0. apply (runax A).
      + apply idpath.
    - unfold dirprodpair. use total2_paths_f; apply idpath.
  Qed.

  Definition ABGR_DirectSumIn2 (A B : abgr) : ABGR⟦B, abgrdirprod A B⟧ :=
    monoidfunconstr (ABGR_DirectSumIn2_ismonoidfun A B).

  Lemma ABGR_DirectSumIdIn1 (A B : abgr) :
    ABGR_DirectSumIn1 A B · ABGR_DirectSumPr1 A B = idabgrfun A.
  Proof.
    use total2_paths_f.
    - cbn. use funextfun. intros x. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumIdIn2 (A B : abgr) :
    ABGR_DirectSumIn2 A B · ABGR_DirectSumPr2 A B = idabgrfun B.
  Proof.
    use total2_paths_f.
    - cbn. use funextfun. intros x. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumUnel1 (A B : abgr) :
    ABGR_DirectSumIn1 A B · ABGR_DirectSumPr2 A B = ABGR_zero_arrow A B.
  Proof.
    use total2_paths_f.
    - cbn. use funextfun. intros x. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumUnel2 (A B : abgr) :
    ABGR_DirectSumIn2 A B · ABGR_DirectSumPr1 A B = ABGR_zero_arrow B A.
  Proof.
    use total2_paths_f.
    - cbn. use funextfun. intros x. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  Lemma ABGR_DirectSumId (A B : abgr) :
    ABGR_hombinop _ _ (ABGR_DirectSumPr1 A B · ABGR_DirectSumIn1 A B)
                  (ABGR_DirectSumPr2 A B · ABGR_DirectSumIn2 A B) = idabgrfun _.
  Proof.
    use total2_paths_f.
    - cbn. use funextfun. intros x.
      apply dirprodeq.
      + apply (runax A).
      + apply (lunax B).
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Hide isAdditive behind Qed. *)
  Definition ABGR_isAdditive : isAdditive ABGR_PreAdditive.
  Proof.
    use (mk_isAdditive ABGR_PreAdditive ABGR_has_zero).
    intros X Y.
    use BinDirectSums.mk_BinDirectSumCone.
    - exact (abgrdirprod X Y).
    - exact (ABGR_DirectSumIn1 _ _).
    - exact (ABGR_DirectSumIn2 _ _).
    - exact (ABGR_DirectSumPr1 _ _).
    - exact (ABGR_DirectSumPr2 _ _).
    - use BinDirectSums.mk_isBinDirectSumCone.
      (* BinProduct *)
      + use (bincoproducts.mk_isBinCoproductCocone _ has_homsets_ABGR).
        intros Z f g.
        use (unique_exists); cbn.
        (* Construction of the morphism from X ⊕ Y to Z. *)
        use monoidfunconstr.
        * exact (pr1(ABGR_hombinop _ _ (ABGR_DirectSumPr1 X Y · f) (ABGR_DirectSumPr2 X Y · g))).
        * split.
          -- intros x x'. cbn. unfold funcomp. cbn.
             rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 g)).
             repeat rewrite <- (assocax (abgrtoabmonoid Z)). apply ropeq.
             repeat rewrite (assocax (abgrtoabmonoid Z)). apply lopeq.
             apply (pr2 (pr2 Z)).
          -- cbn. unfold funcomp. cbn.
             set (HH := pr2 (pr2 f)). cbn in HH. rewrite -> HH.
             set (HHg := pr2 (pr2 g)). cbn in HHg. rewrite HHg.
             apply (runax (abgrtoabmonoid Z)).
        (* Commutativity of the morphism. *)
        * split.
          -- use total2_paths_f.
             ++ cbn. apply funextfun. intros x.
                unfold funcomp. cbn. set (HHg := pr2 (pr2 g)). cbn in HHg. rewrite HHg.
                apply (runax (abgrtoabmonoid Z)).
             ++ apply proofirrelevance. apply isapropismonoidfun.
          -- use total2_paths_f.
             ++ cbn. apply funextfun. intros x.
                unfold funcomp. cbn. set (HHf := pr2 (pr2 f)). cbn in HHf. rewrite HHf.
                apply (lunax (abgrtoabmonoid Z)).
             ++ apply proofirrelevance. apply isapropismonoidfun.
        (* Equality on equality of homsets *)
        * intros y. apply isapropdirprod; exact (has_homsets_ABGR _ _ _ _).
        (* Uniqueness *)
        * intros y z. use total2_paths_f.
          -- cbn. apply funextfun. intros x.
             unfold funcomp. rewrite <- (idabgrfun_left _ _ y).
             rewrite <- (ABGR_DirectSumId X Y). cbn. unfold funcomp.
             rewrite <- (dirprod_pr1 z). rewrite <- (dirprod_pr2 z).
             cbn. unfold funcomp.
             rewrite (runax (abgrtoabmonoid X)). rewrite (lunax (abgrtoabmonoid Y)).
             rewrite <- (pr1 (pr2 y)). cbn.
             rewrite (runax (abgrtoabmonoid X)). rewrite (lunax (abgrtoabmonoid Y)).
             apply idpath.
          -- apply proofirrelevance. apply isapropismonoidfun.
      (* BinCoproduct *)
      + use (binproducts.mk_isBinProductCone _ has_homsets_ABGR).
        intros Z f g.
        use (unique_exists); cbn.
        (* Construction of the morphism from Z to X ⊕ Y. *)
        * use monoidfunconstr.
          --  exact (pr1( ABGR_hombinop _ _ (f · ABGR_DirectSumIn1 X Y)
                                        (g · ABGR_DirectSumIn2 X Y))).
          -- split.
             ++ intros x x'. cbn. apply dirprodeq.
                ** cbn. repeat rewrite (runax (abgrtoabmonoid X)).
                   rewrite (pr1 (pr2 f)). apply idpath.
                ** cbn. repeat rewrite (lunax (abgrtoabmonoid Y)).
                   rewrite (pr1 (pr2 g)). apply idpath.
             ++ apply dirprodeq.
                ** cbn. set (HHf := pr2 (pr2 f)). cbn in HHf. rewrite HHf.
                   apply (runax (abgrtoabmonoid X)).
                ** cbn. set (HHg := pr2 (pr2 g)). cbn in HHg. rewrite HHg.
                   apply (lunax (abgrtoabmonoid Y)).
        (* Commutativity of the morphism. *)
        * split.
          -- use total2_paths_f.
             ++ cbn. apply funextfun. intros x.
                unfold funcomp. cbn. rewrite (runax (abgrtoabmonoid X)). apply idpath.
             ++ apply proofirrelevance. apply isapropismonoidfun.
          -- use total2_paths_f.
             ++ cbn. apply funextfun. intros x.
                unfold funcomp. cbn. rewrite (lunax (abgrtoabmonoid Y)). apply idpath.
             ++ apply proofirrelevance. apply isapropismonoidfun.
        (* Equality on equality of homsets *)
        * intros y. apply isapropdirprod; exact (has_homsets_ABGR _ _ _ _).
        (* Uniqueness *)
        * intros y z. use total2_paths_f.
          -- cbn. apply funextfun. intros x.
             rewrite <- (idabgrfun_right _ _ y).
             rewrite <- (ABGR_DirectSumId X Y). cbn.
             rewrite <- (dirprod_pr1 z). rewrite <- (dirprod_pr2 z). cbn.
             apply idpath.
          -- apply proofirrelevance. apply isapropismonoidfun.
      (* Id1 *)
      + use total2_paths_f.
        * apply funextfun. intros x. cbn. apply idpath.
        * apply proofirrelevance. apply isapropismonoidfun.
      (* Id2 *)
      + use total2_paths_f.
        * apply funextfun. intros x. cbn. apply idpath.
        * apply proofirrelevance. apply isapropismonoidfun.
      (* Unit1 *)
      + use total2_paths_f.
        * apply funextfun. intros x. cbn. apply idpath.
        * apply proofirrelevance. apply isapropismonoidfun.
      (* Unit2 *)
      + use total2_paths_f.
        * apply funextfun. intros x. cbn. apply idpath.
        * apply proofirrelevance. apply isapropismonoidfun.
      (* Id *)
      + use total2_paths_f.
        * apply funextfun. intros x. induction x.
          cbn. apply dirprodeq.
          -- cbn. apply (runax (abgrtoabmonoid X)).
          -- cbn. apply (lunax (abgrtoabmonoid Y)).
        * apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Construction of Additive from ABGR. *)
  Definition ABGR_Additive : Additive := mk_Additive ABGR_PreAdditive ABGR_isAdditive.

End ABGR_Additive.


(** * Kernels and Cokernels
    In the following section we construct Kernels and Cokernels in ABGR. *)
Section ABGR_kernels.


  (** ** Kernels *)

  (** Shows that kernel of f is a subgroup of f. *)
  Definition ABGR_kernel_subabgr_issubgr {A B : abgr} (f : monoidfun A B) :
    issubgr (ABGR_kernel_hsubtype f).
  Proof.
    split.
    (* issubmonoid *)
    - split.
      + intros a a'.  induction a as [a1 a2]. induction a' as [a'1 a'2].
        cbn in *. rewrite (pr1 (pr2 f)). unfold ishinh_UU in *.
        intros P X. apply (a2 P). intros a3. apply (a'2 P). intros a'3. apply X.
        cbn in *. rewrite a3. rewrite a'3. apply (runax (abgrtoabmonoid B)).
      + intros P X. apply X. cbn in *. rewrite <- (pr2 (pr2 f)). apply idpath.
    (* inverse *)
    - intros x a. unfold ABGR_kernel_hsubtype in *. rewrite (monoidfuninvtoinv f x).
      cbn in *. unfold ishinh_UU in *. intros P X. apply a. intros X1.
      rewrite -> X1 in X. apply X. apply (grinvunel B).
  Qed.

  (** Construction of the kernel of f. *)
  Definition ABGR_kernel_subabgr {A B : abgr} (f : monoidfun A B) : @subabgr A
    := subgrconstr (@ABGR_kernel_hsubtype A B f) (ABGR_kernel_subabgr_issubgr f).

  (** Hide ismonoidfun behind Qed. *)
  Definition ABGR_kernel_monoidfun_ismonoidfun {A B : abgr} (f : monoidfun A B) :
    @ismonoidfun (ABGR_kernel_subabgr f) A
                 (inclpair (pr1carrier (ABGR_kernel_hsubtype f))
                           (isinclpr1carrier (ABGR_kernel_hsubtype f))).
  Proof.
    split.
    - intros a a'. apply idpath.
    - apply idpath.
  Qed.

  (** Construction of the morphism from the kernel of A to A. *)
  Definition ABGR_kernel_monoidfun {A B : abgr} (f : monoidfun A B) :
    ABGR⟦carrierofasubabgr (ABGR_kernel_subabgr f), A⟧
    := monoidincltomonoidfun
         (ABGR_kernel_subabgr f) A
         (@monoidmonopair (ABGR_kernel_subabgr f) A
                          (inclpair (pr1carrier (ABGR_kernel_hsubtype f))
                                    (isinclpr1carrier (ABGR_kernel_hsubtype f)))
                          (ABGR_kernel_monoidfun_ismonoidfun f)).

  (** Hide equality for kernel behind Qed. *)
  Definition ABGR_Kernel_eq {A B : abgr} (f : monoidfun A B) :
    ABGR_kernel_monoidfun f · f = ZeroArrow ABGR_has_zero _ _.
  Proof.
    use total2_paths_f.
    - apply funextfun. intros x. induction x as [t p]. cbn.
      unfold funcomp, pr1carrier. cbn in p. cbn.
      use (squash_to_prop p).
      + exact (setproperty _ _ _).
      + intros X. rewrite ABGR_has_zero_to. cbn.
        rewrite ABGR_has_zero_from. cbn.
        exact X.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Construction of the unique arrow to the kernel object. *)
  Definition ABGR_KernelArrowIn {A B C : ABGR} (h : C --> A) (f : A --> B)
             (H : h · f = ABGR_zero_arrow C B) :
    ABGR⟦C, carrierofasubabgr (ABGR_kernel_subabgr f)⟧.
  Proof.
    use monoidfunconstr.
    - apply base_paths in H. cbn in H. unfold funcomp in H.
      intros c. cbn. unfold ABGR_kernel_hsubtype. cbn.
      refine (tpair _ (pr1 h c) _). cbn.
      unfold ishinh_UU. intros P X. apply X.
      apply (funeqpaths H c).
    (* ismonoidfun *)
    - split.
      + intros y y'. cbn. use total2_paths_f.
        * cbn. rewrite (pr1 (pr2 h)). apply idpath.
        * apply proofirrelevance. cbn. apply isapropishinh.
      + use total2_paths_f.
        * cbn. apply (pr2 (pr2 h)).
        * apply proofirrelevance. cbn. apply isapropishinh.
  Defined.

  (** Hide isEqualizer behind Qed. *)
  Definition ABGR_Kernel_isKernel {A B : abgr} (f : ABGR⟦A, B⟧) :
    isKernel ABGR_has_zero (ABGR_kernel_monoidfun f) f (ABGR_Kernel_eq f).
  Proof.
    induction A as [t p]. induction B as [t' p'].
    use (mk_isKernel has_homsets_ABGR).
    intros w h H'. induction w as [tt pp]. induction h as [tt' pp'].
    use unique_exists.
    (* Construction of the unique arrow into kernel *)
    - rewrite (ABGR_has_zero_arrow_eq _ _) in H'.
      apply (ABGR_KernelArrowIn _ f H').
    (* Commutativity of the kernel arrow *)
    - use total2_paths_f.
      + apply funextfun. intros x. cbn. apply idpath.
      + apply proofirrelevance. apply isapropismonoidfun.
    (* Equality of equalities of morphisms *)
    - intros y. exact (has_homsets_ABGR _ _ _ _).
    (* Uniqueness *)
    - intros y t3. induction y as [t1 p1]. apply base_paths in t3. cbn in *.
      unfold pr1carrier, funcomp in t3. cbn in t3. use total2_paths_f.
      + cbn. apply funextfun. intros x. use total2_paths_f.
        * cbn. exact (funeqpaths t3 x).
        * apply proofirrelevance. apply isapropishinh.
      + apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Construction of a kernel of a morphism of abelian groups f. *)
  Definition ABGR_Kernel {A B : abgr} (f : monoidfun A B) : Kernel ABGR_has_zero f :=
    mk_Kernel (ABGR_has_zero) (ABGR_kernel_monoidfun f) f (ABGR_Kernel_eq f)
              (ABGR_Kernel_isKernel f).

  (** As a corollary we get that ABGR has kernels. *)
  Corollary ABGR_kernels : Kernels ABGR_has_zero.
  Proof.
    intros A B f. exact (ABGR_Kernel f).
  Defined.


  (** ** Cokernels *)


  (** A proof that the image of f is a subgroup of B. *)
  Definition ABGR_image_issubgr {A B : abgr} (f : monoidfun A B) : issubgr (ABGR_image_hsubtype f).
  Proof.
    split.
    (* issubmonoid *)
    - split.
      + intros a a'. induction a as [a1 a2]. induction a' as [a'1 a'2].
        cbn in *. unfold ishinh_UU in *.
        intros P X. apply (a2 P). intros a3. apply (a'2 P). intros a'3. apply X.
        cbn in *. use tpair. induction a3 as [t p]. induction a'3 as [t0 p0].
        apply (op t t0). cbn. (* unfold total2_rect. *)
        induction a3 as [t p]. induction a'3 as [t0 p0]. rewrite (pr1 (pr2 f)). cbn in *.
        rewrite p. rewrite p0. apply idpath.
      + intros P X. apply X. use tpair.
        * exact (unel A).
        * cbn. rewrite <- (pr2 (pr2 f)). apply idpath.
    (* inverse *)
    - intros x a. unfold ABGR_image_hsubtype in *. unfold ishinh in *. cbn in *.
      unfold ishinh_UU in *. intros P X. apply a. intros X1. apply X.
      induction X1 as [t p]. use tpair. apply (grinv A t). cbn.
      set (XXt := monoidfuninvtoinv f t). cbn in XXt.
      rewrite XXt. rewrite p. apply idpath.
  Qed.

  (** Construction of the image of f. *)
  Definition ABGR_image {A B : abgr} (f : monoidfun A B) : @subabgr B :=
    @subgrconstr B (@ABGR_image_hsubtype A B f) (ABGR_image_issubgr f).

  (** A construction of an equivalence relation on B. *)
  Definition ABGR_cokernel_eqrel_istrans {A B : abgr} (f : monoidfun A B) :
    istrans (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 x2 x3 y1 y2.
    unfold ishinh in *. cbn in *. unfold ishinh_UU in *. intros P X.
    apply y1. intros Y1. apply y2. intros Y2. induction Y1 as [t p], Y2 as [t0 p0]. apply X.
    refine (tpair _ (op t t0) _). rewrite (pr1 (pr2 f)). cbn in *.
    rewrite p. rewrite p0.

    rewrite <- (assocax (abgrtoabmonoid B)).
    rewrite (assocax (abgrtoabmonoid B) x1 _ _).
    rewrite (grlinvax B). rewrite (runax B).
    apply idpath.
  Qed.

  Definition ABGR_cokernel_eqrel_isrefl {A B : abgr} (f : monoidfun A B) :
    isrefl (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 y1 y2. apply y2. refine (tpair _ (unel A) _).
    rewrite (grrinvax B). rewrite <- (pr2 (pr2 f)). apply idpath.
  Qed.

  Definition ABGR_cokernel_eqrel_issymm {A B : abgr} (f : monoidfun A B) :
    issymm (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 x2 x3 y1 y2.
    unfold ishinh in *. cbn in *. unfold ishinh_UU in *. apply x3.
    intros X3. apply y2. induction X3 as [t p]. refine (tpair _ (grinv A t) _).
    set (XXf := (grinvandmonoidfun A B (pr2 f) t)). cbn in XXf.
    rewrite XXf. rewrite p.
    set (XXB := grinvop B x1 (grinv B x2)). cbn in XXB.
    rewrite XXB. rewrite grinvinv. apply idpath.
  Qed.

  (** The eqrel on B used to form the cokernel of f. *)
  Definition ABGR_cokernel_eqrel {A B : abgr} (f : monoidfun A B) : eqrel B :=
    @eqrelconstr  B (fun b1 : B => fun b2 : B => ∃ a : A, (f a) = (op b1 (grinv B b2)))
                  (ABGR_cokernel_eqrel_istrans f)
                  (ABGR_cokernel_eqrel_isrefl f)
                  (ABGR_cokernel_eqrel_issymm f).


  (** Hide isbinoprel behind Qed. *)
  Definition ABGR_cokernel_abgr_isbinoprel {A B : abgr} (f : monoidfun A B) :
    isbinophrel (λ b1 b2 : pr1 B, ∃ a : pr1 A, pr1 f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    use isbinophrelif.
    - apply (pr2 (pr2 B)).
    - intros x1 x2 x3 y1. cbn in *. unfold ishinh_UU in *. intros P X.
      apply y1. intros Y1. induction Y1 as [t p]. apply X.
      refine (tpair _ t _). rewrite p. rewrite ((pr2 (pr2 B)) x3 _).
      rewrite (assocax B). apply lopeq. rewrite ((pr2 (pr2 B)) x3 _).
      rewrite grinvop. rewrite (assocax B). rewrite (grlinvax B).
      rewrite (runax B). apply idpath.
  Qed.

  (** Construction of the cokernel of f. We need to take the quotient group of B by the image of
      f. *)
  Definition ABGR_cokernel_abgr {A B : abgr} (f : monoidfun A B) : abgr :=
    @abgrquot B (binopeqrelpair (ABGR_cokernel_eqrel f) (ABGR_cokernel_abgr_isbinoprel f)).

  (** Construction of the monoidfun from B to the cokernel of f. *)
  Definition ABGR_cokernel_monoidfun {A B : abgr} (f : monoidfun A B) :
    ABGR⟦B, ABGR_cokernel_abgr f⟧.
  Proof.
    use monoidfunconstr.
    - use (setquotpr (ABGR_cokernel_eqrel f)).

    (* ismonoidfun *)
    - split.
      + split.
      + apply idpath.
  Defined.

  (** ABGR Equality for cokernels. *)
  Definition ABGR_cokernel_eq {A B : abgr} (f : ABGR⟦A, B⟧) :
    f · ABGR_cokernel_monoidfun f = ZeroArrow ABGR_has_zero A (ABGR_cokernel_abgr f).
  Proof.
    rewrite ABGR_has_zero_arrow_eq.
    use total2_paths_f.
    - apply funextfun. intros a. apply (iscompsetquotpr (ABGR_cokernel_eqrel f)).
      unfold ABGR_cokernel_eqrel.
      intros P X. cbn in *. apply X. refine (tpair _ a _).
      use (pathscomp0 (pathsinv0 (runax B (pr1 f a)))).
      apply lopeq.
      use (pathscomp0 (pathsinv0 (grinvunel B))).
      apply maponpaths. apply idpath.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** The following result is used to show that map from setquot is a monoidfun. *)
  Definition isbinopfun_2of3 {A B C : setwithbinop} (f : (pr1 A) -> (pr1 B))
             (g : (pr1 B) -> (pr1 C)) (H : issurjective f) :
    isbinopfun (g ∘ f)%functions -> isbinopfun f -> isbinopfun g.
  Proof.
    intros h f'.
    intros b1 b2.
    unfold issurjective in H. cbn in H.
    set (H1 := H b1).
    set (H2 := H b2).
    use (squash_to_prop H1). exact (pr2 (pr1 C) _ _).
    intros HH1.
    use (squash_to_prop H2). exact (pr2 (pr1 C) _ _).
    intros HH2.
    unfold hfiber in *. induction HH1 as [t p]. induction HH2 as [t0 p0].
    rewrite <- p. rewrite <- p0. rewrite <- f'. cbn.

    assert (X : g (f (t * t0)%multmonoid) = (g ∘ f)%functions (t * t0)%multmonoid).
    {
      unfold funcomp. apply idpath.
    }
    cbn in X. rewrite X.

    rewrite h. unfold funcomp. apply idpath.
  Qed.

  (** We show that the function is compatible with the relation. This is used to get the unique
      CokernelOut map. *)
  Definition ABGR_CokernelArrowOutUniv_iscomprelfun {A B C : ABGR} (f : A --> B) (h : B --> C)
             (H : (λ x : pr1 A, (pr1 h) (pr1 f x)) = (λ _ : pr1 A, 1%multmonoid)) :
    iscomprelfun (λ b1 b2 : pr1 B, ∃ a : pr1 A, pr1 f a = (b1 * grinv (abgrtogr B) b2)%multmonoid)
                 (pr1 h).
  Proof.
    intros x x' X.
    use (squash_to_prop X). exact (pr2 (pr1 (pr1 C)) _ _).
    intros X'. induction X' as [t p].
    set (Y := funeqpaths H t). cbn in Y.
    apply (maponpaths (pr1 h)) in p. cbn in *.
    rewrite Y in p. rewrite (pr1 (pr2 h)) in p.
    apply (grrcan (abgrtogr C) ((pr1 h) (grinv (abgrtogr B) x'))).
    cbn in *.
    rewrite <- p. rewrite <- (pr1 (pr2 h)). apply pathsinv0.
    rewrite (grrinvax (abgrtogr B) x'). apply (pr2 (pr2 h)).
  Qed.

  (** Construction of the unique arrow out of the cokernel. *)
  Definition ABGR_CokernelArrowOutUniv {A B C : ABGR} (f : A --> B) (h : B --> C)
             (H : (λ x : pr1 A, (pr1 h) (pr1 f x)) = (λ _ : pr1 A, 1%multmonoid)) :
    (ABGR_cokernel_abgr f) -> (pr1 C) :=
    setquotuniv
         (λ b1 b2 : pr1 B, ∃ a : pr1 A, pr1 f a = (b1 * grinv (abgrtogr B) b2)%multmonoid)
         (pr1 C) (pr1 h) (ABGR_CokernelArrowOutUniv_iscomprelfun f h H).

  (** Hide isCoequalizer behind Qed. *)
  Definition ABGR_isCokernel {A B : abgr} (f : ABGR⟦A, B⟧) :
    isCokernel ABGR_has_zero f (ABGR_cokernel_monoidfun f) (ABGR_cokernel_eq f).
  Proof.
    use (mk_isCokernel (has_homsets_ABGR)).
    intros w h H'.
    use unique_exists.
    (* Construction of the unique arrow out of cokernel *)
    - use monoidfunconstr.
      + rewrite (ABGR_has_zero_arrow_eq _ _) in H'.
        apply base_paths in H'. cbn in H'. unfold funcomp in H'.
        apply (ABGR_CokernelArrowOutUniv f _ H').
        (* ismonoidfun *)
      + split.
        * use isbinopfun_2of3.
          -- apply (pr1 B).
          -- apply (pr1 (ABGR_cokernel_monoidfun f)).
          -- apply issurjsetquotpr.
          -- unfold funcomp. apply (pr2 h).
          -- apply (pr2 (ABGR_cokernel_monoidfun f)).
        * cbn. set (XXh := pr2 (pr2 h)). cbn in XXh. rewrite <- XXh. apply idpath.
      (* Commutativity *)
    - use total2_paths_f.
      + cbn. apply funextfun. intros b. apply idpath.
      + apply proofirrelevance. apply isapropismonoidfun.
    (* Equality on equality of morphisms *)
    - intros y. cbn. intros x x'. apply (has_homsets_ABGR).
    (* Uniqueness *)
    - intros y. induction y as [t p]. intros  t0. cbn in t0.
      use total2_paths_f.
      + cbn. apply funextfun. intros z. cbn in *.
        set (surj := issurjsetquotpr (ABGR_cokernel_eqrel f)).
        unfold issurjective in surj. cbn in surj.
        set (surjz := surj z).
        use (squash_to_prop surjz). exact (pr2 (pr1 (pr1 w)) _ _).
        intros surjz'. unfold hfiber in surjz'. induction surjz' as [t1 p0].
        rewrite <- p0. cbn. apply base_paths in t0. cbn in t0.
        unfold funcomp in t0. apply (funeqpaths t0 t1).
      + apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Construction of a cokernel of a morphism of abelian groups f. *)
  Definition ABGR_Cokernel {A B : abgr} (f : ABGR⟦A, B⟧) : Cokernel ABGR_has_zero f :=
    mk_Cokernel ABGR_has_zero f (ABGR_cokernel_monoidfun f) (ABGR_cokernel_eq f)
                (ABGR_isCokernel f).

  (** As a corollary we get that ABGR has cokernels. *)
  Corollary ABGR_cokernels : Cokernels ABGR_has_zero.
  Proof.
    intros A B f. apply (ABGR_Cokernel f).
  Defined.

End ABGR_kernels.


(** * Monics are inclusions and Epis are surjections
    In this section we show that Monics are inclusions and Epis are surjections in ABGR. *)
Section ABGR_monics.

  (** First we need to construct a monoidfun from hzaddabgr to A to show that Monics are inclusions
      in ABGR. *)
  Definition ABGR_natset_map {A : abgr} (a : A) : natset -> A.
  Proof.
    intros n. induction n as [|n IHn].
    - apply (unel A).
    - apply (@op A a IHn).
  Defined.

  Definition ABGR_natset_dirprod_map {A : abgr} (a : A) : natset × natset -> A.
  Proof.
    intros n.
    exact (@op A (ABGR_natset_map a (dirprod_pr1 n)) (ABGR_natset_map (grinv A a) (dirprod_pr2 n))).
  Defined.

  Definition ABGR_natset_map_S {A : abgr} (a : A) (n : nat) :
    ABGR_natset_map a (S n) = (ABGR_natset_map a n * a)%multmonoid.
  Proof.
    induction n as [|n IHn].
    - cbn. rewrite (lunax A). apply (runax A).
    - cbn. rewrite (assocax A). apply lopeq. apply (commax A).
  Qed.

  Definition ABGR_natset_map_plus {A : abgr} (a : A) (n m : nat) :
    ABGR_natset_map a (n + m) = (ABGR_natset_map a n * ABGR_natset_map a m)%multmonoid.
  Proof.
    induction n as [|n IHn].
    - rewrite (lunax A). apply idpath.
    - cbn. rewrite (assocax A). apply lopeq.
      unfold ABGR_natset_map in *. cbn in IHn.
      rewrite IHn. apply idpath.
  Qed.

  Definition ABGR_natset_dirprod_abmonoid_map {A : abgr} (a : A) :
    (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)) -> A.
  Proof.
    exact (ABGR_natset_dirprod_map a).
  Defined.

  Definition ABGR_natset_dirprod_map_isbinopfun {A : abgr} (a : A) :
    isbinopfun (ABGR_natset_dirprod_abmonoid_map a).
  Proof.
    unfold ABGR_natset_dirprod_abmonoid_map.
    set (tmp1 := ABGR_natset_map_plus a).
    set (tmp2 := ABGR_natset_map_plus (grinv A a)).
    intros x x'. unfold ABGR_natset_dirprod_map.
    unfold ABGR_natset_map in *. cbn in *.
    rewrite tmp1. rewrite tmp2. unfold dirprod_pr1. unfold dirprod_pr2.
    repeat rewrite (assocax A). apply lopeq.
    repeat rewrite <- (assocax A). apply ropeq.
    apply (commax A).
  Qed.

  Definition ABGR_natset_dirprod_map_binopfun {A : abgr} (a : A) :
    binopfun (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)) A.
  Proof.
    use binopfunpair.
    exact (ABGR_natset_dirprod_map a).
    exact (ABGR_natset_dirprod_map_isbinopfun a).
  Defined.

  Definition ABGR_natset_dirprod_map_monoidfun_unel_eq {A : abgr} (a : A) :
    ABGR_natset_dirprod_map
      a (unel (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig))) = (unel A).
  Proof.
    unfold ABGR_natset_dirprod_map. cbn. apply (runax A).
  Qed.

  Definition ABGR_natset_dirprod_map_monoidfun {A : abgr} (a : A) :
    monoidfun (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)) A.
  Proof.
    use monoidfunconstr.
    - exact (ABGR_natset_dirprod_map a).
    - split.
      + exact (ABGR_natset_dirprod_map_isbinopfun a).
      + exact (ABGR_natset_dirprod_map_monoidfun_unel_eq a).
  Defined.

  (** Construction of the monoidfun from nat × nat to integers. *)
  Definition ABGR_natset_to_Z_monoidfun :
    monoidfun (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)) hzaddabgr.
  Proof.
    use monoidfunconstr.
    - use setquotpr.
    (* ismonoidfun *)
    - split.
      + split.
      + apply idpath.
  Defined.

  Definition ABGR_natset_dirprod_map_ind {A : abgr} (a : A) (n m : nat) :
    ABGR_natset_dirprod_map a (n + m,,m) = ABGR_natset_dirprod_map a (n,, 0).
  Proof.
    induction m as [|m IHm].
    - rewrite natpluscomm. cbn. apply idpath.
    - rewrite natplusnsm. cbn.
      unfold ABGR_natset_dirprod_map. cbn.
      rewrite <- (assocax A).
      rewrite (commax A _ (grinv A a)).
      rewrite <- (assocax A).
      rewrite (grlinvax A). rewrite (lunax A).
      unfold ABGR_natset_dirprod_map in IHm. cbn in IHm.
      apply IHm.
  Qed.

  Definition ABGR_natset_dirprod_map_ind2 {A : abgr} (a : A) (n1 n2 m k : nat) :
    ABGR_natset_dirprod_map a (n1,,m) = ABGR_natset_dirprod_map a (n2,,k) ->
    ABGR_natset_dirprod_map a (n1,,S m) = ABGR_natset_dirprod_map a (n2,,S k).
  Proof.
    unfold ABGR_natset_dirprod_map. cbn. intros H.
    rewrite (commax A (grinv A a)). rewrite (commax A (grinv A a)).
    rewrite <- (assocax A). rewrite <- (assocax A).
    apply ropeq. apply H.
  Qed.

  Definition ABGR_integer_map_iscomprelfun {A : abgr} (a : A) :
    iscomprelfun (binopeqrelabgrdiff (rigaddabmonoid natcommrig)) (ABGR_natset_dirprod_map a).
  Proof.
    intros x. induction x as [t p]. induction p as [|p IHp].
    - intros x'. induction x' as [t0 p]. induction p as [|p IHp].
      + intros H. cbn in *. use (squash_to_prop H). exact (setproperty A _ _).
        intros H'. induction H' as [t1 p]. repeat rewrite natplusassoc in p. cbn in p.
        apply natplusrcan in p. rewrite p. apply idpath.
      + intros H. cbn in *. use (squash_to_prop H). exact (setproperty A _ _).
        intros H'. induction H' as [t1 p0]. rewrite (natplusassoc _ 0) in p0. cbn in p0.
        apply natplusrcan in p0. rewrite <- p0.
        rewrite ABGR_natset_dirprod_map_ind. apply idpath.
    - intros x'. induction x' as [t0 p0]. induction p0 as [|p0 IHp0].
      + intros H. cbn in *. use (squash_to_prop H). exact (setproperty A _ _).
        intros H'. induction H' as [t1 p0]. rewrite natplusassoc in p0. cbn in p0.
        apply natplusrcan in p0. rewrite p0.
        rewrite ABGR_natset_dirprod_map_ind. apply idpath.
      + intros H. cbn in *. use (squash_to_prop H). exact (setproperty A _ _).
        intros H'. induction H' as [t1 p1]. apply natplusrcan in p1.
        repeat rewrite natplusnsm in p1. cbn in p1.
        apply invmaponpathsS in p1.
        set (tmp := IHp (t0,,p0)). cbn in tmp.
        assert (tmp1 : ishinh_UU(∑ x0 : nat, t + p0 + x0 = t0 + p + x0)).
        {
          unfold ishinh_UU. intros P X. apply X.
          refine (tpair _ 0 _).
          rewrite natpluscomm. cbn.
          rewrite (natpluscomm _ 0). cbn. exact p1.
        }
        set (tmp2 := tmp tmp1).
        apply ABGR_natset_dirprod_map_ind2.
        exact tmp2.
  Qed.

  (** Construction of tha map \mathbb{Z} --> A, 1 ↦ a *)
  Definition ABGR_integer_map {A : abgr} (a : A) : hzaddabgr -> A.
  Proof.
    use setquotuniv.
    - exact (ABGR_natset_dirprod_map a).
    - exact (ABGR_integer_map_iscomprelfun a).
  Defined.

  (** Hide ismonoidfun behind Qed. *)
  Definition ABGR_integer_map_ismonoidfun {A : abgr} (a : A) : ismonoidfun (ABGR_integer_map a).
  Proof.
    split.
    (* isbinopfun *)
    - use isbinopfun_2of3.
      + apply (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)).
      + apply (ABGR_natset_to_Z_monoidfun).
      + apply issurjsetquotpr.
      + unfold funcomp. apply (pr2 (ABGR_natset_dirprod_map_binopfun a)).
      + apply (pr2 (ABGR_natset_to_Z_monoidfun)).
    (* unel *)
    - unfold ABGR_integer_map. cbn.
      unfold ABGR_natset_dirprod_map. cbn.
      apply (runax A).
  Qed.

  (** Construction of the monoidfun \mathbb{Z} --> A, 1 ↦ a *)
  Definition ABGR_integer_map_monoidfun {A : abgr} (a : A) : monoidfun hzaddabgr A.
  Proof.
    use monoidfunconstr.
    - exact (ABGR_integer_map a).
    - exact (ABGR_integer_map_ismonoidfun a).
  Defined.


  (** ** Epis *)

  (** hfiber (pr1 f) b is inhabited. *)
  Definition ABGR_epi_hfiber_inhabited {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) (b : B)
             (H : setquotpr (ABGR_cokernel_eqrel f) b =
                  setquotpr (ABGR_cokernel_eqrel f) 1%multmonoid) : ∥ hfiber (pr1 f) b ∥.
  Proof.
    set (tmp := weqpathsinsetquot (ABGR_cokernel_eqrel f) b (unel _)).
    set (tmp1 := pr1weq (invweq tmp) H).
    unfold ABGR_cokernel_eqrel in tmp1. cbn in tmp1.
    intros P X. apply tmp1. intros Y. apply X. induction Y as [t p].
    rewrite grinvunel in p.
    rewrite (runax B) in p.
    apply (hfiberpair (pr1 f) t p).
  Qed.

  (** This result shows that Epis are surjective. *)
  Definition ABGR_epi_issurjective {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) :
    issurjective (pr1 f).
  Proof.
    unfold isEpi in isE.
    set (tmp := isE (ABGR_cokernel_abgr f) (ABGR_cokernel_monoidfun f)
                    (ABGR_zero_arrow B (ABGR_cokernel_abgr f))).
    assert (H : f · ABGR_cokernel_monoidfun f = f · ABGR_zero_arrow B (ABGR_cokernel_abgr f)).
    {
      rewrite ABGR_cokernel_eq.
      rewrite <- ABGR_has_zero_arrow_eq.
      rewrite ZeroArrow_comp_right.
      apply idpath.
    }
    set (tmp1 := tmp H).
    intros x.
    unfold ABGR_cokernel_monoidfun in tmp1. unfold ABGR_zero_arrow in tmp1.
    cbn in tmp1. apply base_paths in tmp1. cbn in tmp1.
    set (tmp2 := @funeqpaths (pr1 B) (pr1 (ABGR_cokernel_abgr f))).
    set (tmp3 := tmp2 _ _ tmp1). cbn in tmp3.
    apply (ABGR_epi_hfiber_inhabited f isE x (tmp3 x)).
  Qed.


  (** ** Monics *)

  (** The following equalities are needed to prove that Monics are inclusions. *)
  Lemma ABGR_natset_dirprod_monoidfun_eq {A B : abgr} (a1 a2 : A) (f : monoidfun A B)
        (H : f a1 = f a2) : monoidfuncomp (ABGR_natset_dirprod_map_monoidfun a1) f =
                            monoidfuncomp (ABGR_natset_dirprod_map_monoidfun a2) f.
  Proof.
    use total2_paths_f.
    - cbn. unfold funcomp. apply funextfun.
      intros x. induction x as [t p]. induction t as [|t IHt].
      + induction p as [|p IHp].
        (* p = 0 *)
        * unfold ABGR_natset_dirprod_map. cbn.
          rewrite (runax A). apply idpath.
        (* Inductive step on p. *)
        * unfold ABGR_natset_dirprod_map. cbn.
          rewrite (lunax A). rewrite (lunax A).
          rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 f)).
          apply (maponpaths (fun h : _ => grinv B h)) in H.
          rewrite <- (monoidfun_inv f a1) in H.
          rewrite <- (monoidfun_inv f a2) in H.
          cbn in *. rewrite <- H. apply lopeq.
          unfold ABGR_natset_dirprod_map in IHp. cbn in IHp.
          rewrite (lunax A) in IHp. rewrite (lunax A) in IHp. apply IHp.
      (* Inductive step on t. *)
      + unfold ABGR_natset_dirprod_map in *.
        unfold ABGR_natset_map in *. cbn in *.
        rewrite (assocax A). rewrite (assocax A).
        set (tmp := (pr1 (pr2 f))). cbn in tmp.
        rewrite tmp. rewrite (tmp a2). rewrite H.
        apply lopeq. apply IHt.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Precomposing with surjective monoidfun preserves equality. *)
  Lemma ABGR_monoidfun_precomp {A :abmonoid} {B C : abgr} (f1 f2 : monoidfun B C)
        (g : monoidfun A B) (H : issurjective (pr1 g)) :
    monoidfuncomp g f1 = monoidfuncomp g f2 -> f1 = f2.
  Proof.
    intros X.
    use total2_paths_f.
    - apply funextfun. intros x. apply base_paths in X. cbn in X. unfold funcomp in X.
      unfold issurjective in H.
      use (squash_to_prop (H x)). use (setproperty C).
      intros h. induction h as [t p]. rewrite <- p.
      apply (funeqpaths X t).
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Commutativity of the natset_dirprod_map with natset_to_Z and integer_map. *)
  Lemma ABGR_integer_natset_map_comm {A : abgr} (a : A) :
    monoidfuncomp ABGR_natset_to_Z_monoidfun (ABGR_integer_map_monoidfun a) =
    ABGR_natset_dirprod_map_monoidfun a.
  Proof.
    use total2_paths_f.
    - cbn. apply funextfun. intros x. unfold funcomp. use setquotunivcomm.
    - apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** Equality of monoidfun compositions. *)
  Lemma ABGR_integer_map_monoifun_eq {A B : abgr} (a1 a2 : A) (f : monoidfun A B)
        (H : f a1 = f a2) : monoidfuncomp (ABGR_integer_map_monoidfun a1) f =
                            monoidfuncomp (ABGR_integer_map_monoidfun a2) f.
  Proof.
    apply (@ABGR_monoidfun_precomp
             (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig))
             hzaddabgr B
             (monoidfuncomp (ABGR_integer_map_monoidfun a1) f)
             (monoidfuncomp (ABGR_integer_map_monoidfun a2) f)
             ABGR_natset_to_Z_monoidfun).
    use issurjsetquotpr.

    set (e1 := abmonoidfuncomp_assoc
                 (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig))
                 hzaddabgr A B ABGR_natset_to_Z_monoidfun (ABGR_integer_map_monoidfun a1) f).
    apply pathsinv0 in e1. use (pathscomp0 e1). clear e1.

    set (e2 := abmonoidfuncomp_assoc
                 (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig))
                 hzaddabgr A B ABGR_natset_to_Z_monoidfun (ABGR_integer_map_monoidfun a2) f).
    use (pathscomp0 _ e2). clear e2.

    set (e3 := ABGR_integer_natset_map_comm a1).
    apply (maponpaths (fun h : _ => monoidfuncomp h f)) in e3.
    use (pathscomp0 e3). clear e3.

    set (e4 := ABGR_integer_natset_map_comm a2).
    apply (maponpaths (fun h : _ => monoidfuncomp h f)) in e4.
    apply pathsinv0 in e4. use (pathscomp0 _ e4). clear e4.

    apply ABGR_natset_dirprod_monoidfun_eq.
    apply H.
  Qed.

  (** Finally we are able to show that monics are inclusions. *)
  Definition ABGR_monic_isincl {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f) : isincl (pr1 f).
  Proof.
    intros b h1 h2.
    use iscontrpair.
    - use total2_paths_f.
      + unfold isMonic in isM. cbn in *.
        set (p := pr2 h1). cbn in p.
        set (p' := pr2 h2). cbn in p'.
        rewrite <- p' in p.
        set (tmp := isM hzaddabgr (ABGR_integer_map_monoidfun (pr1 h1))
                        (ABGR_integer_map_monoidfun (pr1 h2))
                        (ABGR_integer_map_monoifun_eq (pr1 h1) (pr1 h2) f p)).
        apply base_paths in tmp. cbn in tmp.
        set (tmp2 := funeqpaths tmp).
        set (tmp3 := tmp2 (hzone)). cbn in tmp3.
        unfold rigtorngunel2int in tmp3. cbn in tmp3.
        unfold ABGR_natset_dirprod_map in tmp3. cbn in tmp3.
        rewrite <- (runax A). rewrite <- (runax A).
        use (pathscomp0 _ tmp3).
        rewrite (runax A). rewrite (runax A). apply idpath.
      + apply proofirrelevance. exact (setproperty B _ _).
    - intros t1. apply proofirrelevance.
      assert (Hfiber: isaset (hfiber (pr1 f) b)).
      {
        unfold hfiber.
        apply isaset_total2.
        - apply (setproperty A).
        - intros x. apply isasetaprop. exact (setproperty B _ _).
      }
      exact (Hfiber _ _).
  Qed.

End ABGR_monics.


(** * Monics are Kernels and Epis are Cokernels
    In this section we prove that Monics are kernels in ABGR. *)
Section ABGR_monic_kernels.


  (** ** Monics *)

  (** Construction of ishinh_UU hfiber. *)
  Definition ABGR_monic_kernel_hfiber_prop {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f)
             (w : abgr) (x : w) (h: ABGR⟦w, B⟧)
             (H : h · CokernelArrow (ABGR_Cokernel f) = ZeroArrow ABGR_has_zero _ _) :
    ishinh_UU (∑ a : pr1 A, pr1 f a = pr1 h x %multmonoid).
  Proof.
    rewrite ABGR_has_zero_arrow_eq in H.
    cbn in H. unfold ABGR_zero_arrow in H.
    apply base_paths in H. cbn in H. unfold funcomp in H.
    set (tmp1 := (weqpathsinsetquot (ABGR_cokernel_eqrel f) (pr1 h x) (unel _))).
    set (tmp2 := pr1weq (invweq tmp1)).
    set (tmp3 := tmp2 (funeqpaths H x)).
    cbn in tmp3.
    rewrite (grinvunel B) in tmp3.
    rewrite (runax B) in tmp3.
    exact tmp3.
  Qed.

  (** Suppose f is a Monic and h is a morphism to the targe of f so that h composed with the
      cokernel of f is zero, then for any element in the image of h the hfiber consists of exactly
      of one term. We use this to define the unique map KernelIn which is needed to show that f is
      the kernel of its cokernel. *)
  Definition ABGR_monic_kernel_in_hfiber_iscontr {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f)
             (w : abgr) (h: ABGR⟦w, B⟧)
             (H : h · CokernelArrow (ABGR_Cokernel f) = ZeroArrow ABGR_has_zero _ _) :
    ∏ x : w, iscontr (hfiber (pr1 f) (pr1 h x)).
  Proof.
    intros x.
    use (squash_to_prop (ABGR_monic_kernel_hfiber_prop f isM w x h H)).
    apply isapropiscontr.
    intros X.
    apply (iscontrpair (hfiberpair (pr1 f) (pr1 X) (pr2 X))).
    (* Equality in hfibers *)
    intros t.
    use total2_paths_f.
    - cbn.
      assert (e : pr1 f (pr1 t) = pr1 f (pr1 X)).
      {
        cbn. cbn in X, t.
        rewrite (pr2 X).
        apply (pr2 t).
      }
      set (iw := (isweqonpathsincl _ (ABGR_monic_isincl f isM)) (pr1 t) (pr1 X) e).
      unfold hfiber in iw. unfold iscontr in iw. apply (pr1 (pr1 iw)).
    - apply proofirrelevance. exact (setproperty B _ _).
  Qed.

  (** We construct an hfiber for every element in the image of h. *)
  Definition ABGR_monic_kernel_in_hfiber {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f)
             (w : abgr) (x : w) (h: ABGR⟦w, B⟧)
             (H : h · CokernelArrow (ABGR_Cokernel f) = ZeroArrow ABGR_has_zero _ _) :
    hfiber (pr1 f) (pr1 h x).
  Proof.
    use (squash_to_prop (ABGR_monic_kernel_hfiber_prop f isM w x h H)).
    - apply isapropifcontr. apply (ABGR_monic_kernel_in_hfiber_iscontr f isM w h H x).
    - intros X. exact X.
  Qed.

  (** Hide equality behind Qed. *)
  Lemma ABGR_monic_kernel_in_hfiber_mult_eq {A B : abgr} (f : ABGR⟦A, B⟧) (w : abgr) (x x' : w)
        (h : ABGR⟦w, B⟧) (X : hfiber (pr1 f) (pr1 h x)) (X0 : hfiber (pr1 f) (pr1 h x')):
    pr1 f (pr1 X * pr1 X0)%multmonoid = pr1 h (x * x')%multmonoid.
  Proof.
    rewrite (pr1 (pr2 f)).
    rewrite (pr2 X).
    rewrite (pr2 X0).
    rewrite (pr1 (pr2 h)).
    apply idpath.
  Qed.

  (** This is used to verify that KernelIn is a binopfun. *)
  Definition ABGR_monic_kernel_in_hfiber_mult {A B : abgr} (f : ABGR⟦A, B⟧) (w : abgr) (x x' : w)
             (h : ABGR⟦w, B⟧) : hfiber (pr1 f) (pr1 h x) -> hfiber (pr1 f) (pr1 h x') ->
                                hfiber (pr1 f) (pr1 h (x * x')%multmonoid).
  Proof.
    intros X X0.
    exact (hfiberpair (pr1 f) ((pr1 X) * (pr1 X0))%multmonoid
                      (ABGR_monic_kernel_in_hfiber_mult_eq f w x x' h X X0)).
  Defined.

  (** Hide equality behind Qed. *)
  Lemma ABGR_monic_kernel_in_hfiber_unel_eq {A B : abgr} (f : ABGR⟦A, B⟧) (w : abgr)
        (h : ABGR⟦w, B⟧) : pr1 f 1%multmonoid = pr1 h 1%multmonoid.
  Proof.
    rewrite (pr2 (pr2 h)).
    apply (pr2 (pr2 f)).
  Qed.

  (** This is used to vefiry that KernelIn respects unit elements. *)
  Definition ABGR_monic_kernel_in_hfiber_unel {A B : abgr} (f : ABGR⟦A, B⟧) (w : abgr)
             (h : ABGR⟦w, B⟧) : hfiber (pr1 f) (pr1 h 1%multmonoid) :=
    hfiberpair (pr1 f) 1%multmonoid (ABGR_monic_kernel_in_hfiber_unel_eq f w h).

  (** We define the KernelIn as the morphism x : w ↦ pr1 (hfiber (pr1 f) (pr1 h x)) : A. *)
  Definition ABGR_monic_kernel_in {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f) (w : abgr)
             (h: ABGR⟦w, B⟧)
             (H : h · CokernelArrow (ABGR_Cokernel f) = ZeroArrow ABGR_has_zero _ _) : w -> A.
  Proof.
    intros x.
    exact (pr1 (ABGR_monic_kernel_in_hfiber f isM w x h H)).
  Defined.

  (** Hide ismonoidfun behind Qed. *)
  Definition ABGR_monic_kernel_in_ismonoidfun {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f)
             (w : abgr) (h: ABGR⟦w, B⟧)
             (H : h · CokernelArrow (ABGR_Cokernel f) = ZeroArrow ABGR_has_zero _ _) :
    ismonoidfun (ABGR_monic_kernel_in f isM w h H).
  Proof.
    unfold ABGR_monic_kernel_in. cbn in *.
    split.
    (* isbinopfun *)
    - intros x x'.
      set (tmp := ABGR_monic_kernel_in_hfiber_mult
                    f w x x' h
                    (ABGR_monic_kernel_in_hfiber f isM w x h H)
                    (ABGR_monic_kernel_in_hfiber f isM w x' h H)).

      assert (e : (ABGR_monic_kernel_in_hfiber f isM w (x * x')%multmonoid h H) = tmp).
      {
        set (tmp2 := ABGR_monic_kernel_in_hfiber_iscontr f isM w h H (x * x')%multmonoid).
        unfold iscontr in tmp2. cbn in tmp2.
        rewrite ((pr2 tmp2) tmp).
        rewrite ((pr2 tmp2) (ABGR_monic_kernel_in_hfiber f isM w (x * x')%multmonoid h H)).
        apply idpath.
      }
      apply base_paths in e. use (pathscomp0 e). unfold tmp.
      unfold ABGR_monic_kernel_in_hfiber_mult. cbn. apply idpath.
    - assert (e : (ABGR_monic_kernel_in_hfiber f isM w 1%multmonoid h H)
                  = (ABGR_monic_kernel_in_hfiber_unel f w h) ).
      {
        set (tmp2 := ABGR_monic_kernel_in_hfiber_iscontr f isM w h H 1%multmonoid).
        unfold iscontr in tmp2. cbn in tmp2.
        rewrite ((pr2 tmp2) (ABGR_monic_kernel_in_hfiber_unel f w h)).
        rewrite ((pr2 tmp2) (ABGR_monic_kernel_in_hfiber f isM w 1%multmonoid h H)).
        apply idpath.
      }
      apply base_paths in e. use (pathscomp0 e). apply idpath.
  Qed.

  (** We show that the KernelIn map is a monoidfun. *)
  Definition ABGR_monic_kernel_in_monoidfun {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f)
             (w : abgr) (h: ABGR⟦w, B⟧)
             (H : h · CokernelArrow (ABGR_Cokernel f) = ZeroArrow ABGR_has_zero _ _) :
    monoidfun w A := monoidfunconstr (ABGR_monic_kernel_in_ismonoidfun f isM w h H).

  (** ** We are ready to prove that Monics are Kernels. *)

  (** Hide equality behind Qed. *)
  Definition ABGR_Monic_Kernel_eq {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f) :
    f · CokernelArrow (ABGR_Cokernel f) = ZeroArrow ABGR_has_zero A (ABGR_Cokernel f).
  Proof.
    apply CokernelCompZero.
  Qed.

  (** Hide isEqualizer beind Qed. *)
  Definition ABGR_Monic_Kernel_isKernel {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f) :
    isKernel ABGR_has_zero f (CokernelArrow (ABGR_Cokernel f))
             (CokernelCompZero ABGR_has_zero (ABGR_Cokernel f)).
  Proof.
    use (mk_isKernel has_homsets_ABGR).
    intros w h H'.
    use unique_exists.
    (* KernelIn *)
    - apply (ABGR_monic_kernel_in_monoidfun f isM w h H').
    (* Commutativity *)
    - cbn. use total2_paths_f.
      + cbn. unfold funcomp. apply funextfun.
        intros x. cbn. unfold ABGR_monic_kernel_in.
        set (tmp := pr2 ((ABGR_monic_kernel_in_hfiber f isM w x h H'))).
        cbn in tmp. apply tmp.
      + apply proofirrelevance. apply isapropismonoidfun.
    (* Equality in equalities of morphisms *)
    - intros y. exact (has_homsets_ABGR _ _ _ _).
    (* Uniqueness *)
    - intros y H. cbn in H.
      unfold isMonic in isM. apply isM. cbn. rewrite H.
      use total2_paths_f.
      + cbn. apply funextfun. intros x.
        apply pathsinv0. unfold funcomp. unfold ABGR_monic_kernel_in.
        apply (pr2 ((ABGR_monic_kernel_in_hfiber f isM w x h H'))).
      + apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** We construct a Kernel from the monic f so that the KernelArrow = f. *)
  Definition ABGR_monic_kernel {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f) :
    Kernel ABGR_has_zero (CokernelArrow (ABGR_Cokernel f)) :=
    mk_Kernel ABGR_has_zero f (CokernelArrow (ABGR_Cokernel f))
              (ABGR_Monic_Kernel_eq f isM) (ABGR_Monic_Kernel_isKernel f isM).

  (** We verify that f is the KernelArrow of the above Kernel. *)
  Definition ABGR_monic_kernel_KernelArrow {A B : abgr} (f : ABGR⟦A, B⟧) (isM : isMonic f) :
    KernelArrow (ABGR_monic_kernel f isM) = f.
  Proof.
    apply idpath.
  Qed.


  (** ** Epis *)

  (** Constructs a kernel_hsubtype. *)
  Definition ABGR_epi_cokernel_out_kernel_hsubtype {A B : abgr} (f : ABGR⟦A, B⟧) (a : A)
             (H : pr1 f a = 1%multmonoid) : ABGR_kernel_hsubtype f.
  Proof.
    unfold ABGR_kernel_hsubtype. cbn.
    use (tpair _ a _). cbn.
    unfold ishinh_UU. intros P X.
    apply X. apply H.
  Defined.

  (** Equality we are going to need. *)
  Lemma ABGR_epi_cokernel_out_data_eq {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) (w : abgr)
        (h : ABGR⟦A,w⟧)
        (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero (ABGR_Kernel f) w) :
    ∏ x : ABGR_kernel_hsubtype f, pr1 h (pr1carrier (ABGR_kernel_hsubtype f) x) = 1%multmonoid.
  Proof.
    rewrite ABGR_has_zero_arrow_eq in H.
    cbn in H. unfold ABGR_zero_arrow in H.
    apply base_paths in H. cbn in H.
    unfold funcomp in H.
    apply (funeqpaths H).
  Qed.

  (** hfibers of the same element to unel. *)
  Lemma ABGR_epi_cokernel_out_data_hfibers_to_unel {A B : abgr} (f : ABGR⟦A, B⟧)
        (b : B) (hfib1 hfib2 : hfiber (pr1 f) b) :
    (pr1 f) ((pr1 hfib1) * (grinv A (pr1 hfib2)))%multmonoid = unel B.
  Proof.
    rewrite (pr1 (pr2 f)).
    apply (grrcan (abgrtogr B) (pr1 f (pr1 hfib2))).
    rewrite (assocax B). rewrite <- (pr1 (pr2 f)).
    rewrite (grlinvax A). rewrite (pr2 (pr2 f)).
    rewrite (runax B). rewrite (lunax B).
    rewrite (pr2 hfib1). rewrite (pr2 hfib2).
    apply idpath.
  Qed.

  (** Equality on hfibers. *)
  Lemma ABGR_epi_cokernel_out_data_hfiber_eq {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f)
        (w : abgr) (h : ABGR⟦A,w⟧)
        (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _)
        (b : B) (X : hfiber (pr1 f) b) :
    ∏ hfib : hfiber (pr1 f) b, pr1 h (pr1 hfib) = pr1 h (pr1 X).
  Proof.
    intros hfib.
    set (e1 := ABGR_epi_cokernel_out_data_hfibers_to_unel f b hfib X).
    apply (grrcan (abgrtogr w) (grinv (abgrtogr w) (pr1 h (pr1 X)))).
    rewrite (grrinvax w).
    set (tmp1 := (monoidfun_inv h (pr1 X))). cbn in tmp1.
    apply (maponpaths (fun k : _ => ((pr1 h (pr1 hfib)) * k)%multmonoid)) in tmp1.
    apply pathsinv0 in tmp1. use (pathscomp0 tmp1).
    rewrite <- (pr1 (pr2 h)).
    set (tmp2 := ABGR_epi_cokernel_out_data_eq f isE w h H).
    set (tmp3 := ABGR_epi_cokernel_out_kernel_hsubtype
                   f (pr1 hfib * grinv A (pr1 X))%multmonoid e1).
    set (tmp4 := tmp2 tmp3). cbn in tmp4. apply tmp4.
  Qed.

  (** Suppose that f is an epi and h a morphism from the domain of f such that composition with the
      kernel of f is zero. Then for all terms b of the domain of f, the space of terms of the target
      of h, such that all hfibers of b are mapped to the target, is contractible. *)
  Lemma ABGR_epi_cokernel_out_data_iscontr {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) (w : abgr)
        (h : ABGR⟦A, w⟧) (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) :
    ∏ b : B, iscontr ( ∑ x : w, ∏ (hfib : hfiber (pr1 f) b), pr1 h (pr1 hfib) = x).
  Proof.
    intros b.
    use (squash_to_prop (ABGR_epi_issurjective f isE b)).
    apply isapropiscontr.
    intros X.
    use unique_exists.
    (* The object *)
    - exact (pr1 h (pr1 X)).
    (* Equality of hfibers *)
    - cbn. apply (ABGR_epi_cokernel_out_data_hfiber_eq f isE w h H b X).
    (* Equality on equalities of elements. *)
    - intros y. apply impred_isaprop. intros t. exact (setproperty w _ _).
    (* Uniqueness. *)
    - intros y T. apply (pathsinv0 (T X)).
  Qed.

  (** Using the above result we construct the unique term of w such that all the hfibers of b are
      mapped to it. *)
  Lemma ABGR_epi_cokernel_out_data {A B : abgr} (b : B) (f : ABGR⟦A, B⟧) (isE : isEpi f) (w : abgr)
        (h : ABGR⟦A,w⟧) (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) :
    ( ∑ x : w, ∏ (hfib : hfiber (pr1 f) b), pr1 h (pr1 hfib) = x).
  Proof.
    use (squash_to_prop (ABGR_epi_issurjective f isE b)).
    apply isapropifcontr.
    apply (ABGR_epi_cokernel_out_data_iscontr f isE w h H b).
    intros X.
    apply (unique_exists (pr1 h (pr1 X))).
    (* Equality of hfibers *)
    - apply (ABGR_epi_cokernel_out_data_hfiber_eq f isE w h H b X).
    (* Equality on equalities of elements. *)
    - intros y. apply impred_isaprop. intros t. exact (setproperty w _ _).
    (* Uniqueness *)
    - intros y T. apply (pathsinv0 (T X)).
  Qed.

  (** Construction of the cokernel out map. *)
  Definition ABGR_epi_cokernel_out_map {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) (w : abgr)
             (h : ABGR⟦A,w⟧)
             (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) : B -> w.
  Proof.
    intros b.
    exact (pr1 (ABGR_epi_cokernel_out_data b f isE w h H)).
  Defined.

  (** Hide equality behind Qed. *)
  Definition ABGR_epi_cokernel_out_data_mult_eq {A B : abgr} (b1 b2 : B) (f : ABGR⟦A, B⟧)
             (isE : isEpi f) (w : abgr) (h : ABGR⟦A, w⟧)
             (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _)
             (X : ∑ x : w, ∏ hfib : hfiber (pr1 f) b1, pr1 h (pr1 hfib) = x)
             (X0 : ∑ x : w, ∏ hfib : hfiber (pr1 f) b2, pr1 h (pr1 hfib) = x) :
    ∏ hfib : hfiber (pr1 f) (b1 * b2)%multmonoid, pr1 h (pr1 hfib) = (pr1 X * pr1 X0)%multmonoid.
  Proof.
    intros hfib.
    use (squash_to_prop (ABGR_epi_issurjective f isE b1)).
    exact (setproperty w _ _). intros X1.
    use (squash_to_prop (ABGR_epi_issurjective f isE b2)).
    exact (setproperty w _ _). intros X2.
    rewrite <- ((pr2 X) X1). rewrite <- ((pr2 X0) X2). rewrite <- (pr1 (pr2 h)).
    exact (ABGR_epi_cokernel_out_data_hfiber_eq
             f isE w h H (b1 * b2)%multmonoid (hfiber_op f b1 b2 X1 X2) hfib).
  Qed.

  (** This is used to verify that CokernelOut is a binopfun. *)
  Definition ABGR_epi_cokernel_out_data_mult {A B : abgr} (b1 b2 : B) (f : ABGR⟦A, B⟧)
             (isE : isEpi f) (w : abgr) (h : ABGR⟦A, w⟧)
             (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) :
    ( ∑ x : w, ∏ (hfib : hfiber (pr1 f) b1), pr1 h (pr1 hfib) = x) ->
    ( ∑ x : w, ∏ (hfib : hfiber (pr1 f) b2), pr1 h (pr1 hfib) = x) ->
    ( ∑ x : w, ∏ (hfib : hfiber (pr1 f) (b1 * b2)%multmonoid), pr1 h (pr1 hfib) = x).
  Proof.
    intros X X0.
    exact (tpair _ ((pr1 X) * (pr1 X0))%multmonoid
                 (ABGR_epi_cokernel_out_data_mult_eq b1 b2 f isE w h H X X0)).
  Defined.

  (** Hide equality behind Qed. *)
  Definition ABGR_epi_cokernel_out_data_unel_eq {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f)
             (w : abgr) (h : ABGR⟦A, w⟧)
             (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) :
    ∏ hfib : hfiber (pr1 f) 1%multmonoid, pr1 h (pr1 hfib) = 1%multmonoid.
  Proof.
    intros hfib.
    set (hfib_unel := hfiberpair (pr1 f) 1%multmonoid (pr2 (pr2 f))).
    rewrite (ABGR_epi_cokernel_out_data_hfiber_eq f isE w h H 1%multmonoid hfib_unel hfib).
    cbn. apply (pr2 (pr2 h)).
  Qed.

  (** Construction of a structure for unel. *)
  Definition ABGR_epi_cokernel_out_data_unel {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f)
             (w : abgr) (h : ABGR⟦A, w⟧)
             (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) :
    ( ∑ x : w, ∏ (hfib : hfiber (pr1 f) 1%multmonoid),  pr1 h (pr1 hfib) = x) :=
    tpair _ 1%multmonoid (ABGR_epi_cokernel_out_data_unel_eq f isE w h H).

  (** We show that the cokernel_out_map ismonoidfun. *)
  Lemma ABGR_epi_cokernel_out_ismonoidfun {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) (w : abgr)
        (h : ABGR⟦A,w⟧) (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) :
    ismonoidfun (ABGR_epi_cokernel_out_map f isE w h H).
  Proof.
    split.
    (* isbinopfun *)
    - intros x x'.
      unfold ABGR_epi_cokernel_out_map.
      (* The left hand side is equal to the multiplication of the datas on the right hand side. *)
      set (HH0 := ABGR_epi_cokernel_out_data_mult x x' f isE w h H
                                                  (ABGR_epi_cokernel_out_data x f isE w h H)
                                                  (ABGR_epi_cokernel_out_data x' f isE w h H)).
      assert (HH : ABGR_epi_cokernel_out_data (x * x')%multmonoid f isE w h H = HH0).
      {
        set (tmp := ABGR_epi_cokernel_out_data_iscontr f isE w h H (x * x')%multmonoid).
        rewrite (pr2 tmp). apply pathsinv0. rewrite (pr2 tmp).
        apply idpath.
      }

      apply base_paths in HH.
      use (pathscomp0 HH).
      apply idpath.
    (* unel *)
    - unfold ABGR_epi_cokernel_out_map.
      (* The left hand side is equal to unel. *)
      assert (HH : (ABGR_epi_cokernel_out_data 1%multmonoid f isE w h H)
                   = (ABGR_epi_cokernel_out_data_unel f isE w h H)).
      {
        rewrite (pr2(ABGR_epi_cokernel_out_data_iscontr f isE w h H 1%multmonoid)).
        apply pathsinv0.
        rewrite (pr2(ABGR_epi_cokernel_out_data_iscontr f isE w h H 1%multmonoid)).
        apply idpath.
      }
      apply base_paths in HH. rewrite HH. apply idpath.
  Qed.

  (** Construction of the monoidfun cokernel_out. *)
  Definition ABGR_epi_cokernel_out_monoidfun {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f)
             (w : abgr) (h : ABGR⟦A,w⟧)
             (H : KernelArrow (ABGR_Kernel f) · h = ZeroArrow ABGR_has_zero _ _) :
    monoidfun B w := monoidfunconstr (ABGR_epi_cokernel_out_ismonoidfun f isE w h H).


  (** ** We are ready to prove that Epis are Cokernels. *)

  (** Hide equality behind Qed. *)
  Definition ABGR_epi_cokernel_eq {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) :
    KernelArrow (ABGR_Kernel f) · f = ZeroArrow ABGR_has_zero _ _.
  Proof.
    apply KernelCompZero.
  Qed.

  (** Hide isCoequalizer behind Qed. *)
  Definition ABGR_epi_cokernel_isCokernel {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) :
    isCokernel ABGR_has_zero (KernelArrow (ABGR_Kernel f)) f (ABGR_epi_cokernel_eq f isE).
  Proof.
    use (mk_isCokernel has_homsets_ABGR).
    intros w h H.
    use unique_exists.
    (* Arrow *)
    - exact (ABGR_epi_cokernel_out_monoidfun f isE w h H).
    (* Commutativity *)
    - cbn. use total2_paths_f.
      + cbn. unfold funcomp. apply funextfun.
        intros x. apply pathsinv0. unfold ABGR_epi_cokernel_out_map.
        apply (pr2 ((ABGR_epi_cokernel_out_data (pr1 f x) f isE w h H))
                   (@hfiberpair _ _ (pr1 f) (pr1 f x) x (idpath _))).
      + apply proofirrelevance. apply isapropismonoidfun.
    (* Equality of equalities of morphisms *)
    - intros y. exact (has_homsets_ABGR _ _ _ _).
    (* Uniqueness *)
    - intros y T. cbn in T. unfold isEpi in isE. apply isE. cbn. rewrite T.
      use total2_paths_f.
      + cbn. unfold funcomp. apply funextfun. intros x. unfold ABGR_epi_cokernel_out_map.
        apply (pr2 ((ABGR_epi_cokernel_out_data (pr1 f x) f isE w h H))
                   (@hfiberpair _ _ (pr1 f) (pr1 f x) x (idpath _))).
      + apply proofirrelevance. apply isapropismonoidfun.
  Qed.

  (** We construct a Cokernel such that CokernelArrow = f. *)
  Definition ABGR_epi_cokernel {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) :
    Cokernel ABGR_has_zero (KernelArrow (ABGR_Kernel f)) :=
    mk_Cokernel ABGR_has_zero (KernelArrow (ABGR_Kernel f)) f _
                (ABGR_epi_cokernel_isCokernel f isE).

  (** We verify that f is the CokernelArrow of the above Cokernel. *)
  Definition ABGR_epi_cokernel_CokernelArrow {A B : abgr} (f : ABGR⟦A, B⟧) (isE : isEpi f) :
    CokernelArrow (ABGR_epi_cokernel f isE) = f.
  Proof.
    apply idpath.
  Qed.

End ABGR_monic_kernels.


(** * ABGR is AbelianPreCat
    In this section we put all the previous results together to show that the precategory ABGR,
    consisting of abelian groups, is an AbelianPreCat. *)
Section ABGR_abelianprecat.

  Definition ABGR_AbelianPreCat : AbelianPreCat.
  Proof.
    set (Add := ABGR_Additive).
    set (BinDS := to_BinDirectSums Add).
    use (mk_Abelian ABGR).
    (* Data1 *)
    - unfold Data1.
      split.
      + exact (ABGR_has_zero). (* zero object *)
      + split.
        * intros X Y. exact (BinDirectSum_BinProduct _ (BinDS X Y)). (* BinProducts *)
        * intros X Y. exact (BinDirectSum_BinCoproduct _ (BinDS X Y)). (* BinCoproducts *)
    (* Data *)
    - unfold AbelianData.
      split.
      + unfold Data2.
        split.
        * intros A B f. exact (ABGR_Kernel f). (* Kernels *)
        * intros A B f. exact (ABGR_Cokernel f). (* Cokernels *)
      + split.
        (* Monics are kernels of epis *)
        * use mk_AbelianMonicKernelsData.
          intros x y M.
          set (monic_ker := ABGR_monic_kernel (pr1 M) (pr2 M)).
          use tpair.
          -- use tpair.
             ++ use tpair.
                ** exact (ABGR_Cokernel (pr1 M)).
                ** exact (CokernelArrow (ABGR_Cokernel (pr1 M))).
             ++ use dirprodpair.
                ** exact (CokernelArrowisEpi _ (ABGR_Cokernel (pr1 M))).
                ** exact (KernelCompZero ABGR_has_zero monic_ker).
          -- exact (KernelisKernel _ monic_ker).
        (* Epis are cokernels *)
        * use mk_AbelianEpiCokernelsData.
          intros x y E.
          set (epi_coker := ABGR_epi_cokernel (pr1 E) (pr2 E)).
          use tpair.
          -- use tpair.
             ++ use tpair.
                ** exact (ABGR_Kernel (pr1 E)).
                ** exact (KernelArrow (ABGR_Kernel (pr1 E))).
             ++ use dirprodpair.
                ** exact (KernelArrowisMonic _ (ABGR_Kernel (pr1 E))).
                ** exact (CokernelCompZero ABGR_has_zero epi_coker).
          -- exact (CokernelisCokernel _ epi_coker).
  Defined.

End ABGR_abelianprecat.


Section ABGR_corollaries.

  (** Some applications to Additive categories *)
  Lemma AdditiveZeroArrow_postmor_Abelian {Add : Additive} (x y z : Add) :
    to_postmor_monoidfun Add x y z (ZeroArrow (Additive.to_Zero Add) y z) =
    ZeroArrow (@to_Zero ABGR_AbelianPreCat) (@to_abgrop Add x y) (@to_abgrop Add x z).
  Proof.
    rewrite ABGR_has_zero_arrow_eq.
    unfold to_postmor_monoidfun.
    unfold ABGR_zero_arrow.
    use monoidfun_eq.
    intros g. cbn. unfold to_postmor. cbn.
    rewrite ZeroArrow_comp_right.
    rewrite <- PreAdditive_unel_zero.
    apply idpath.
  Qed.

  Lemma AdditiveZeroArrow_premor_Abelian {Add : Additive} (x y z : Add) :
    to_premor_monoidfun Add x y z (ZeroArrow (Additive.to_Zero Add) x y) =
    ZeroArrow (@to_Zero ABGR_AbelianPreCat) (@to_abgrop Add y z) (@to_abgrop Add x z).
  Proof.
    rewrite ABGR_has_zero_arrow_eq.
    unfold to_premor_monoidfun.
    unfold ABGR_zero_arrow.
    use monoidfun_eq.
    intros g. cbn. unfold to_premor.
    rewrite ZeroArrow_comp_left. rewrite <- PreAdditive_unel_zero.
    apply idpath.
  Qed.

  (** is_iso_premor *)
  Local Lemma ABGR_additive_is_iso_premor_inverses {Add : Additive} (x y z : Add) {f : x --> y}
        (H : is_z_isomorphism f) :
    is_inverse_in_precat ((to_premor_monoidfun Add x y z f) : ABGR_AbelianPreCat⟦_, _⟧)
                         (to_premor_monoidfun Add y x z (is_z_isomorphism_mor H)).
  Proof.
    use mk_is_inverse_in_precat.
    - use monoidfun_eq.
      intros x0. cbn. unfold to_premor. rewrite assoc.
      rewrite (is_inverse_in_precat2 H). apply id_left.
    - use monoidfun_eq.
      intros x0. cbn. unfold to_premor. rewrite assoc.
      rewrite (is_inverse_in_precat1 H). apply id_left.
  Qed.

  Lemma ABGR_Additive_is_iso_premor {Add : Additive} (x y z : Add) {f : x --> y}
        (H : is_z_isomorphism f) :
    @is_z_isomorphism ABGR_AbelianPreCat _ _ (to_premor_monoidfun Add x y z f).
  Proof.
    use mk_is_z_isomorphism.
    - exact (to_premor_monoidfun Add _ _ z (is_z_isomorphism_mor H)).
    - exact (ABGR_additive_is_iso_premor_inverses _ _ z H).
  Defined.

  Local Lemma ABGR_additive_is_iso_postmor_inverses {Add : Additive} (x y z : Add) {f : y --> z}
        (H : is_z_isomorphism f) :
    is_inverse_in_precat ((to_postmor_monoidfun Add x y z f) : ABGR_AbelianPreCat⟦_, _⟧)
                         (to_postmor_monoidfun Add x z y (is_z_isomorphism_mor H)).
  Proof.
    use mk_is_inverse_in_precat.
    - use monoidfun_eq.
      intros x0. cbn. unfold to_postmor. rewrite <- assoc.
      rewrite (is_inverse_in_precat1 H). apply id_right.
    - use monoidfun_eq.
      intros x0. cbn. unfold to_postmor. rewrite <- assoc.
      rewrite (is_inverse_in_precat2 H). apply id_right.
  Qed.

  Lemma ABGR_Additive_is_iso_postmor {Add : Additive} (x y z : Add) {f : y --> z}
        (H : is_z_isomorphism f) :
    @is_z_isomorphism ABGR_AbelianPreCat _ _ (to_postmor_monoidfun Add x y z f).
  Proof.
    use mk_is_z_isomorphism.
    - exact (to_postmor_monoidfun Add x _ _ (is_z_isomorphism_mor H)).
    - exact (ABGR_additive_is_iso_postmor_inverses x _ _ H).
  Defined.

  Local Lemma ABGR_Additive_premor_postmor_is_iso_inverses {Add : Additive} (x y : Add)
        {f : x --> y}
        (H1 : @is_z_isomorphism ABGR_AbelianPreCat _ _ (to_premor_monoidfun Add x y x f))
        (H2 : @is_z_isomorphism ABGR_AbelianPreCat _ _ (to_postmor_monoidfun Add y x y f)) :
    is_inverse_in_precat f ((is_z_isomorphism_mor H1 : monoidfun (to_abgrop x x) (to_abgrop y x))
                              (identity x : to_abgrop x x)).
  Proof.
    set (mor1 := ((is_z_isomorphism_mor H1) : (monoidfun (to_abgrop x x) (to_abgrop y x)))
                   ((identity x) : to_abgrop x x)).
    set (mor2 := ((is_z_isomorphism_mor H2) : (monoidfun (to_abgrop y y) (to_abgrop y x)))
                   ((identity y) : to_abgrop y y)).
    assert (Hx : f · mor1 = identity x).
    {
      set (tmp := is_inverse_in_precat2 H1).
      apply base_paths in tmp.
      cbn in tmp. unfold to_premor, funcomp in tmp.
      set (tmp2 := funeqpaths tmp (identity x)). cbn in tmp2.
      apply tmp2.
    }
    assert (Hy : mor2 · f = identity y).
    {
      set (tmp := is_inverse_in_precat2 H2).
      apply base_paths in tmp. cbn in tmp.
      unfold to_premor, funcomp in tmp.
      set (tmp2 := funeqpaths tmp (identity y)). cbn in tmp2.
      unfold to_postmor in tmp2. cbn. apply tmp2.
    }
    assert (H : mor1 = mor2).
    {
      rewrite <- (id_right mor2).
      rewrite <- Hx.
      rewrite assoc.
      rewrite Hy.
      rewrite id_left.
      apply idpath.
    }
    use mk_is_inverse_in_precat.
    - exact Hx.
    - rewrite H. exact Hy.
  Qed.

  Lemma ABGR_Additive_premor_postmor_is_iso {Add : Additive} (x y : Add) {f : x --> y}
        (H1 : @is_z_isomorphism ABGR_AbelianPreCat _ _ (to_premor_monoidfun Add x y x f))
        (H2 : @is_z_isomorphism ABGR_AbelianPreCat _ _ (to_postmor_monoidfun Add y x y f)) :
    is_z_isomorphism f.
  Proof.
    use mk_is_z_isomorphism.
    - exact (((is_z_isomorphism_mor H1) : (monoidfun (to_abgrop x x) (to_abgrop y x)))
               ((identity x) : to_abgrop x x)).
    - exact (ABGR_Additive_premor_postmor_is_iso_inverses _ _ H1 H2).
  Defined.

  (** A criteria for isKernel which uses only the elements in the abelian group. *)

  Local Opaque ZeroArrow.

  Definition ABGR_isKernel_iscontr {X Y Z : ABGR} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = @ZeroArrow ABGR_AbelianPreCat (@to_Zero ABGR_AbelianPreCat) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic ABGR _ _ f) (W : ABGR) (h : W --> Y)
             (H' : h · g = @ZeroArrow ABGR (@to_Zero ABGR_AbelianPreCat) W Z) (w' : pr1 W) :
    iscontr (∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = pr1 h w').
  Proof.
    cbn in H'. rewrite <- (@PreAdditive_unel_zero (ABGR_PreAdditive)) in H'.
    unfold to_unel in H'.
    assert (e : pr1 g (pr1 h w') = 1%multmonoid).
    {
      apply base_paths in H'. cbn in H'. unfold funcomp in H'.
      unfold monoidfuncomp in H'. cbn in H'.
      set (tmp := @funeqpaths _ _ _ _ H' w'). cbn in tmp.
      exact tmp.
    }
    set (H'' := H (tpair _ (pr1 h w') e)).
    use (squash_to_prop H''). apply isapropiscontr. intros HH.
    induction HH as [H1 H2]. cbn in H2.
    use tpair.
    - use tpair.
      + exact H1.
      + exact H2.
    - cbn. intros T. induction T as [T1 T2].
      use total2_paths_f.
      + cbn.
        apply (isweqonpathsincl _ (ABGR_monic_isincl f isM)).
        cbn in H2. cbn. rewrite H2. rewrite T2. apply idpath.
      + apply proofirrelevance. exact (setproperty _ _ _).
  Qed.

  Definition ABGR_isKernel {X Y Z : ABGR} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = @ZeroArrow ABGR_AbelianPreCat (@to_Zero ABGR_AbelianPreCat) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic ABGR _ _ f) :
    isKernel (@to_Zero ABGR_AbelianPreCat) f g ZA.
  Proof.
    use mk_isKernel.
    - exact has_homsets_ABGR.
    - intros w h H'.
      use unique_exists.
      + use monoidfunconstr.
        * intros w'. exact (pr1 (iscontrpr1 (ABGR_isKernel_iscontr f g ZA H isM w h H' w'))).
        * split.
          -- intros x y.
             apply (isweqonpathsincl _ (ABGR_monic_isincl f isM)).
             set (ff := (binopfunisbinopfun (f : monoidfun _ _))). cbn in ff. rewrite ff. clear ff.
             set (tmp := pr2 (iscontrpr1 (ABGR_isKernel_iscontr
                                            f g ZA H isM w h H' ((x * y)%multmonoid)))).
             cbn in tmp. cbn. rewrite tmp. clear tmp.
             set (tmp := pr2 (iscontrpr1 (ABGR_isKernel_iscontr
                                            f g ZA H isM w h H' (x%multmonoid)))).
             cbn in tmp. cbn. rewrite tmp. clear tmp.
             set (tmp := pr2 (iscontrpr1 (ABGR_isKernel_iscontr
                                            f g ZA H isM w h H' (y%multmonoid)))).
             cbn in tmp. cbn. rewrite tmp. clear tmp.
             apply (binopfunisbinopfun (h : monoidfun _ _)).
          -- apply (isweqonpathsincl _ (ABGR_monic_isincl f isM)).
             set (tmp := pr2 (iscontrpr1 (ABGR_isKernel_iscontr
                                            f g ZA H isM w h H' (unel (w : abgr))))).
             cbn in tmp. cbn. rewrite tmp. clear tmp.
             set (tmp := monoidfununel h). cbn in tmp. rewrite tmp. clear tmp.
             set (tmp := monoidfununel f). cbn in tmp. rewrite <- tmp. clear tmp.
             apply idpath.
      + use monoidfun_eq. cbn. unfold funcomp. intros x.
        exact (pr2 (iscontrpr1 (ABGR_isKernel_iscontr f g ZA H isM w h H' (x%multmonoid)))).
      + intros y. exact (has_homsets_ABGR _ _ _ _).
      + intros y T. cbn in T.
        use monoidfun_eq. cbn. intros x.
        apply (isweqonpathsincl _ (ABGR_monic_isincl f isM)).
        apply base_paths in T. cbn in T. unfold funcomp in T. cbn in T.
        set(T' := funeqpaths T x). cbn in T'. cbn. rewrite T'. clear T'.
        apply pathsinv0.
        exact (pr2 (iscontrpr1 (ABGR_isKernel_iscontr f g ZA H isM w h H' (x%multmonoid)))).
  Qed.

End ABGR_corollaries.
