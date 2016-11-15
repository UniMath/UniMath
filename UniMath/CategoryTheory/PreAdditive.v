(** * Definition of preadditive categories. *)
(** ** Contents
- Definition of preadditive categories [PreAdditive]
- Zero and unit element coincide
- Composition and inverses
- Quotient of PreAdditive
 *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.BinaryOperations.
Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.

Require Import UniMath.CategoryTheory.limits.zero.


(** * Definition of a PreAdditive precategory
   A preadditive precategory is a precategory such that the sets of morphisms are abelian groups and
   pre- and postcomposing with a morphisms is a monoidfun of the abelian groups. *)
Section def_preadditive.

  (** In preadditive category precomposition and postcomposition for any
      morphism yields a morphism of abelian groups. Classically one says that
      composition is bilinear with respect to the abelian groups? *)
  Definition isPreAdditive (PA : PrecategoryWithAbgrops) : UU :=
    (Π (x y z : PA) (f : x --> y), ismonoidfun (to_premor z f))
      × (Π (x y z : PA) (f : y --> z), ismonoidfun (to_postmor x f)).

  Definition mk_isPreAdditive (PA : PrecategoryWithAbgrops)
             (H1 : Π (x y z : PA) (f : x --> y), ismonoidfun (to_premor z f))
             (H2 : Π (x y z : PA) (f : y --> z), ismonoidfun (to_postmor x f)) :
    isPreAdditive PA.
  Proof.
    exact (H1,,H2).
  Defined.

  Definition to_premor_monoid {PWA : PrecategoryWithAbgrops} (iPA : isPreAdditive PWA) :
    Π (x y z : PWA) (f : x --> y), ismonoidfun (to_premor z f) := dirprod_pr1 iPA.

  Definition to_postmor_monoid {PWA : PrecategoryWithAbgrops} (iPA : isPreAdditive PWA) :
    Π (x y z : PWA) (f : y --> z), ismonoidfun (to_postmor x f) := dirprod_pr2 iPA.

  (** Definition of preadditive categories *)
  Definition PreAdditive : UU := Σ PA : PrecategoryWithAbgrops, isPreAdditive PA.

  Definition PreAdditive_PrecategoryWithAbgrops (A : PreAdditive) : PrecategoryWithAbgrops := pr1 A.
  Coercion PreAdditive_PrecategoryWithAbgrops : PreAdditive >-> PrecategoryWithAbgrops.

  Definition mk_PreAdditive (PA : PrecategoryWithAbgrops) (H : isPreAdditive PA) : PreAdditive.
  Proof.
    exact (tpair _ PA H).
  Defined.

  Definition PreAdditive_isPreAdditive (A : PreAdditive) : isPreAdditive A := pr2 A.
  Coercion PreAdditive_isPreAdditive : PreAdditive >-> isPreAdditive.

  Variable A : PreAdditive.

  (** The following give that premor and postmor are linear. *)
  Definition to_premor_linear {x y : A} (z : A) (f : x --> y) :
    isbinopfun (to_premor z f) := dirprod_pr1 (to_premor_monoid A x y z f).

  Definition to_postmor_linear (x : A) {y z : A} (f : y --> z) :
    isbinopfun (to_postmor x f) := dirprod_pr1 (to_postmor_monoid A x y z f).

  (** Following versions are useful when one wants to rewrite equations *)
  Lemma to_premor_linear' {x y z : A} (f : x --> y) (g h : y --> z) :
    f ;; (to_binop y z g h) = to_binop x z (f ;; g) (f ;; h).
  Proof.
    apply to_premor_linear.
  Qed.

  Lemma to_postmor_linear' {x y z : A} (g h : x --> y) (f : y --> z) :
    (to_binop x y g h) ;; f = to_binop x z (g ;; f) (h ;; f).
  Proof.
    apply to_postmor_linear.
  Qed.

  (** The following says that composing with zero object yields a zero object. *)
  Definition to_premor_unel {x y : A} (z : A) (f : x --> y) :
    to_premor z f 1%multmonoid = 1%multmonoid := dirprod_pr2 (to_premor_monoid A x y z f).

  Definition to_postmor_unel (x : A) {y z : A} (f : y --> z) :
    to_postmor x f 1%multmonoid = 1%multmonoid := dirprod_pr2 (to_postmor_monoid A x y z f).

  (** Following versions are useful when one wants to rewrite equations *)
  Lemma to_premor_unel' {x y : A} (z : A) (f : x --> y) : f ;; (to_unel y z) = to_unel x z.
  Proof.
    apply to_premor_unel.
  Qed.

  Lemma to_postmor_unel' (x : A) {y z : A} (f : y --> z) : (to_unel x y) ;; f = to_unel x z.
  Proof.
    apply to_postmor_unel.
  Qed.

End def_preadditive.
Arguments to_premor_linear [A] [x] [y] _ _ _ _.
Arguments to_postmor_linear [A] _ [y] [z] _ _ _.
Arguments to_premor_linear' [A] [x] [y] [z] _ _ _.
Arguments to_postmor_linear' [A] [x] [y] [z] _ _ _.


(** * Zero and unit
   In the following section we prove that if a preadditive category has a zero
   object, then in a homset the unit element is given by the zero arrow *)
Section preadditive_with_zero.

  Variable A : PreAdditive.

  (** Proof that the zero arrow and the unit element coincide *)
  Lemma PreAdditive_unel_zero (Z : Zero A) (x y : A) : to_unel x y = ZeroArrow Z x y.
  Proof.
    unfold ZeroArrow.
    rewrite <- (id_left (ZeroArrowFrom y)).
    assert (identity Z = to_unel Z Z) by apply ZeroEndo_is_identity.
    rewrite -> X. clear X.

    set (Y := to_postmor_unel A Z (@ZeroArrowFrom A Z y)).
    unfold to_postmor in Y. unfold to_unel.
    rewrite Y. clear Y.

    set (Y' := to_premor_unel A y (@ZeroArrowTo A Z x)).
    unfold to_premor in Y'.
    rewrite Y'. clear Y'.

    apply idpath.
  Qed.

End preadditive_with_zero.



(** * Inverses and composition
   Some equations on inverses in PreAdditive categories *)
Section preadditive_inv_comp.

  Variable A : PreAdditive.

  Lemma PreAdditive_invlcomp {x y z : A} (f : A⟦x, y⟧) (g : A⟦y, z⟧) :
    (to_inv x z (f ;; g)) = (to_inv x y f) ;; g.
  Proof.
    use (grrcan (to_abgrop x z) (f ;; g)).
    unfold to_inv at 1. rewrite grlinvax.
    use (pathscomp0 _ (to_postmor_linear' (to_inv x y f) f g)).
    rewrite linvax. rewrite to_postmor_unel'.
    unfold to_unel.
    apply idpath.
  Qed.

  Lemma PreAdditive_invrcomp {x y z : A} (f : A⟦x, y⟧) (g : A⟦y, z⟧) :
    (to_inv _ _ (f ;; g)) = f ;; (to_inv _ _ g).
  Proof.
    use (grrcan (to_abgrop x z) (f ;; g)).
    unfold to_inv at 1. rewrite grlinvax.
    use (pathscomp0 _ (to_premor_linear' f (to_inv y z g) g)).
    rewrite linvax. rewrite to_premor_unel'.
    unfold to_unel.
    apply idpath.
  Qed.

  Lemma PreAdditive_cancel_inv {x y : A} (f g : A⟦x, y⟧) (H : (to_inv _ _ f)  = (to_inv _ _ g)) :
    f = g.
  Proof.
    apply (grinvmaponpathsinv (to_abgrop x y) H).
  Qed.

End preadditive_inv_comp.


(** * Quotient of homsets
   Suppose you have a subgroup for each set of morphisms such that pre- and postcompositions map
   morphisms in a subgroup to another subgroup. Then one can form a new Preadditive category by
   taking the same objects and morphisms as elements of the quotient groups. We call this
   [PreAdditiveQuot]. An example of this construction is when one wants to form the naive homotopy
   category from a category of complexes. *)
Section preadditive_quotient.

  Variable PA : PreAdditive.

  (** For every set morphisms we have a subgroup. *)
  Definition PreAdditiveSubabgrs : UU := Π (x y : ob PA), @subabgrs (to_abgrop x y).

  Hypothesis PAS : PreAdditiveSubabgrs.

  (** Pre- and postcomposing with an element in the subgroups gives an element of a subgroup.
      This is important since we want pre- and postcomposition with unit element to be
      the unit element in the new precategory. *)
  Definition PreAdditiveComps : UU :=
    Π (x y : ob PA),
    (Π (z : ob PA) (f : x --> y) (inf : pr1submonoids _ (PAS x y) f) (g : y --> z),
     pr1submonoids _ (PAS x z) (f ;; g))
      × (Π (z : ob PA) (f : x --> y) (g : y --> z) (ing : pr1submonoids _ (PAS y z) g),
         pr1submonoids _ (PAS x z) (f ;; g)).

  Hypothesis PAC : PreAdditiveComps.

  (** ** Here are some random results copied from category_abgr.v.
     Theses should be deleted, removed, renamed, generalized, or ...*)

  (** The hProp which tells if two elements of A belong to the same equivalence class in A/B *)
  Definition subgrhrel_hprop {A : gr} (B : @subgrs A) (a1 a2 : A) : hProp :=
    hexists (fun b : B => pr1 b = (a1 * grinv A a2)%multmonoid).

  (** Construct a relation using the above hProp *)
  Definition subgrhrel {A : gr} (B : @subgrs A) : @hrel A :=
    (fun a1 : A => fun a2 : A => (subgrhrel_hprop B a1 a2)).

  (** Some equalities *)
  Local Lemma ropeq (X : setwithbinop) (x y z : X) : x = y -> @op X x z = @op X y z.
  Proof.
    intros e. induction e. apply idpath.
  Qed.

  Local Lemma grinvop (Y : gr) :
    Π y1 y2 : Y, grinv Y (@op Y y1 y2) = @op Y (grinv Y y2) (grinv Y y1).
  Proof.
    intros y1 y2.
    apply (grrcan Y y1).
    rewrite (assocax Y). rewrite (grlinvax Y). rewrite (runax Y).
    apply (grrcan Y y2).
    rewrite (grlinvax Y). rewrite (assocax Y). rewrite (grlinvax Y).
    apply idpath.
  Qed.

  (** Let B be a subgroup of A. Then the canonical map A -> A/B is a monoidfun. *)
  Local Lemma abgrquotpr_ismonoidfun {A : abgr} (H : @binopeqrel A) :
    @ismonoidfun A (abgrquot H) (fun a : A => setquotpr H a).
  Proof.
    split.
    - split.
    - apply idpath.
  Qed.

  Local Lemma funeqpaths {X Y : UU} {f g : X -> Y} (e : f = g) : Π (x : X), f x = g x.
  Proof.
    induction e. intros x. apply idpath.
  Qed.

  Local Definition abgrquotpr_monoidfun {A : abgr} (H : @binopeqrel A) : monoidfun A (abgrquot H) :=
    monoidfunconstr (abgrquotpr_ismonoidfun H).

  Local Lemma monoidfun_inv {A B : abgr} (f : monoidfun A B) (a : A) :
    f (grinv A a) = grinv B (f a).
  Proof.
    apply (grlcan B (f a)). rewrite (grrinvax B).
    use (pathscomp0 (pathsinv0 (((pr1 (pr2 f)) a (grinv A a))))).
    rewrite (grrinvax A). apply (pr2 (pr2 f)).
  Qed.

  (** The relation we defined is an equivalence relation *)
  Lemma iseqrel_subgrhrel (A : gr) (B : @subgrs A) : iseqrel (subgrhrel B).
  Proof.
    unfold subgrhrel. unfold subgrhrel_hprop.
    use iseqrelconstr.
    (* istrans *)
    - intros x1 x2 x3 y1 y2. cbn in *. unfold ishinh_UU in *. intros P X.
      apply y1. intros Y1. apply y2. intros Y2.
      induction Y1 as [t p]. induction Y2 as [t0 p0]. apply X.
      use tpair.
      + use tpair.
        * exact (op (pr1 t) (pr1 t0)).
        * exact (pr2subsetswithbinop B t t0).
      + cbn. rewrite p. rewrite p0. rewrite <- (assocax A).
        apply ropeq. rewrite assocax. rewrite grlinvax. rewrite runax.
        apply idpath.
    (* isrefl *)
    - intros x. intros P X. apply X.
      use tpair.
      + exact (unel B).
      + cbn. apply pathsinv0. apply (grrinvax A).
    (* issymm *)
    - intros x y. cbn. unfold ishinh_UU. intros H P X. apply H. intros H'. clear H.
      apply X. clear X. induction H' as [t p].
      use tpair.
      + exact (grinv B t).
      + cbn. rewrite p. clear p. rewrite grinvop. rewrite grinvinv. apply idpath.
  Qed.

  (** The relation we defined respects binary operations. Note that we use commax, thus the proof
      does not work for nonabelian groups. *)
  Lemma isbinopeqrel_subgr_eqrel {A : abgr} (B : @subabgrs A) :
    isbinophrel (eqrelpair (subgrhrel B) (iseqrel_subgrhrel A B)).
  Proof.
    use isbinophrelif.
    - apply (pr2 (pr2 A)).
    - intros a b c X. cbn in *. unfold ishinh_UU in *. intros P X'. apply X.
      intros X''. clear X. apply X'. clear X'.
      use tpair.
      + exact (pr1 X'').
      + cbn. rewrite (pr2 X''). clear X''. clear B. rewrite grinvop.
        rewrite (commax A c). rewrite (assocax A). rewrite (commax A c).
        rewrite (assocax A). rewrite grlinvax. rewrite runax. apply idpath.
  Qed.

  (** Thus the relation is a binopeqrel *)
  Lemma binopeqrel_subgr_eqrel {A : abgr} (B : @subabgrs A) : @binopeqrel A.
  Proof.
    use binopeqrelpair.
    - exact (eqrelpair _ (iseqrel_subgrhrel A B)).
    - exact (isbinopeqrel_subgr_eqrel B).
  Defined.

  (** These are the homsets in our new category. *)
  Definition subabgr_quot {A : abgr} (B : @subabgrs A) : abgr :=
    abgrquot (binopeqrel_subgr_eqrel B).

  Definition QuotPrecategory_homsets (c d : ob PA) : abgr := subabgr_quot (PAS c d).

  Definition QuotPrecategory_ob_mor : precategory_ob_mor :=
    tpair (fun ob : UU => ob -> ob -> UU) (ob PA) (fun A B : ob PA => QuotPrecategory_homsets A B).


  (** ** Composition of morphisms *)

  (** *** Some lemmas *)

  (** If images of f1 and f2 are equal, then f * inv f2 is mapped to unit. *)
  Local Lemma abgrquotpr_rels_to_unel {A : abgr} {f1 f2 : A} {H : @binopeqrel A} {f : abgrquot H}
             (e1 : setquotpr H f1 = f) (e2 : setquotpr H f2 = f) :
    setquotpr H (f1 * grinv A f2)%multmonoid = setquotpr H 1%multmonoid.
  Proof.
    rewrite <- e2 in e1. clear e2.
    apply (maponpaths (fun f : _ => (f * (@grinv (abgrquot H) (setquotpr H f2)))%multmonoid)) in e1.
    rewrite grrinvax in e1. apply e1.
  Qed.

  (** Equality on relation to refl *)
  Local Lemma abgrquotpr_rel_to_refl {A : abgr} {H : @binopeqrel A} {f g : A} (e : H g g = H f g) :
    H f g.
  Proof.
    induction e.
    apply eqrelrefl.
  Qed.

  Local Lemma abgrquotpr_rel_paths {A : abgr} {H : @binopeqrel A} {f g : A}
        (e : setquotpr H f = setquotpr H g) : H f g.
  Proof.
    exact (abgrquotpr_rel_to_refl (! (funeqpaths (base_paths _ _ e)) g)).
  Qed.

  (** *** Morphisms to elements of groups *)
  Local Lemma mor_to_elem {a b : PA} (f : PA⟦a, b⟧) (H : pr1 (PAS a b) f) : carrier (pr1 (PAS a b)).
  Proof.
    use tpair.
    - exact f.
    - exact H.
  Defined.

  Local Lemma to_inv_elem {a b : PA} (f : PA⟦a, b⟧) (H : pr1 (PAS a b) f) : carrier (pr1 (PAS a b)).
  Proof.
    use tpair.
    - exact (@grinv (to_abgrop a b) f).
    - apply (pr2 (pr2 (PAS a b))). exact H.
  Defined.

  Local Lemma to_op_elem {A B : PA} (f g : PA⟦A, B⟧) (H1 : pr1 (PAS A B) f) (H2 : pr1 (PAS A B) g) :
    pr1 (PAS A B) (to_binop A B f g).
  Proof.
    set (tmp := pr1 (pr1 (pr2 (PAS A B)))). cbn in tmp. unfold issubsetwithbinop in tmp.
    set (a := mor_to_elem f H1). set (a' := mor_to_elem g H2).
    apply (tmp a a').
  Qed.

  (** *** Composition of morphisms in the quotient precategory *)

  Local Lemma QuotPrecategory_comp_iscontr_PAS_eq {A : abgr} {a b c : A}
        (e : a = (b * (grinv A c))%multmonoid) : b = (a * c)%multmonoid.
  Proof.
    rewrite e. rewrite assocax. rewrite grlinvax. rewrite runax. apply idpath.
  Qed.

  Lemma QuotPrecategory_comp_iscontr_PAS {A B C : PA} {t : pr1 (PAS A B)} {t' : pr1 (PAS B C)}
        {f1 f'1 : PA⟦A, B⟧} {g1 g'1 : PA⟦B, C⟧}
        (p : pr1 t = to_binop A B f'1 (grinv (to_abgrop A B) f1))
        (p' : pr1 t' = to_binop B C g'1 (grinv (to_abgrop B C) g1)) :
    pr1 (PAS A C) (to_binop A C (f1 ;; g1) (grinv (to_abgrop A C) (f'1 ;; g'1))).
  Proof.
    set (e1 := QuotPrecategory_comp_iscontr_PAS_eq p).
    set (e2 := QuotPrecategory_comp_iscontr_PAS_eq p').
    rewrite e1. rewrite e2. clear e1 e2 p p'. cbn.
    rewrite to_premor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    set (ac := assocax (to_abgrop A C)). unfold isassoc in ac. cbn in ac.
    set (comm := commax (to_abgrop A C)). unfold iscomm in comm. cbn in comm.
    rewrite (comm _ (f1 ;; g1)). rewrite <- (ac _ (f1 ;; g1) _).
    rewrite (comm _ (f1 ;; g1)). rewrite ac. rewrite ac.
    set (i := grinvop (to_abgrop A C)). cbn in i. rewrite i. repeat rewrite <- ac.
    rewrite comm. rewrite <- ac.
    set (il := linvax _ (f1 ;; g1)). unfold to_inv in il. rewrite il. clear il.
    set (lu := to_lunax A C). unfold islunit in lu. cbn in lu. unfold to_unel. rewrite lu.

    set (tmp := pr2 (pr2 (PAS A C))). cbn in tmp. apply tmp. clear tmp.
    use to_op_elem.
    - use to_op_elem.
      + apply (dirprod_pr1 (PAC A B) C (pr1 t) (pr2 t) (pr1 t')).
      + apply (dirprod_pr2 (PAC A B) C f1 (pr1 t') (pr2 t')).
    - apply (dirprod_pr1 (PAC A B) C (pr1 t) (pr2 t) g1).
  Qed.

  (** The following Lemma is used to define composition of morphisms in the quotient precategory.
      It shows that composition is well defined in QuotPrecategory_ob_mor. *)
  Lemma QuotPrecategory_comp_iscontr {A B C : ob PA} (f : QuotPrecategory_ob_mor⟦A, B⟧)
             (g : QuotPrecategory_ob_mor⟦B, C⟧) :
    iscontr (Σ h : QuotPrecategory_ob_mor⟦A, C⟧,
                   (Π (f' : PA⟦A, B⟧) (e1 : setquotpr _ f' = f)
                      (g' : PA⟦B, C⟧) (e2 : setquotpr _ g' = g), setquotpr _ (f' ;; g') = h)).
  Proof.
    cbn in *.
    set (f'1 := @issurjsetquotpr (to_abgrop A B) (binopeqrel_subgr_eqrel (PAS A B)) f).
    set (g'1 := @issurjsetquotpr (to_abgrop B C) (binopeqrel_subgr_eqrel (PAS B C)) g).
    use (squash_to_prop f'1). apply isapropiscontr. intros f''1. clear f'1.
    use (squash_to_prop g'1). apply isapropiscontr. intros g''1. clear g'1.
    induction f''1 as [f'1 f''1]. induction g''1 as [g'1 g''1]. cbn in *.
    use unique_exists.
    - use (setquotpr (binopeqrel_subgr_eqrel (PAS A C)) (f'1 ;; g'1)).
    - intros f1 Hf g1 Hg. cbn.
      apply (iscompsetquotpr (eqrelpair _ (iseqrel_subgrhrel (to_abgrop A C) (PAS A C)))).
      set (HH := @abgrquotpr_rels_to_unel
                   (to_abgrop A B) f'1 f1 (binopeqrel_subgr_eqrel (PAS A B)) f f''1 Hf).
      set (HH' := @abgrquotpr_rels_to_unel
                    (to_abgrop B C) g'1 g1 (binopeqrel_subgr_eqrel (PAS B C)) g g''1 Hg).
      apply abgrquotpr_rel_paths in HH. apply abgrquotpr_rel_paths in HH'.
      use (squash_to_prop HH). apply propproperty. intros HHH. clear HH.
      use (squash_to_prop HH'). apply propproperty. intros HHH'. clear HH'.
      cbn in HHH. cbn in HHH'. induction HHH as [t p]. induction HHH' as [t' p'].
      rewrite grinvunel in p. rewrite grinvunel in p'.
      set (tmp := to_runax A B). unfold isrunit in tmp. cbn in tmp. rewrite tmp in p. clear tmp.
      set (tmp := to_runax B C). unfold isrunit in tmp. cbn in tmp. rewrite tmp in p'. clear tmp.
      cbn. unfold ishinh_UU. intros P X. apply X. clear X P.
      use tpair.
      + use tpair.
        * exact (to_binop A C (f1 ;; g1) (grinv (to_abgrop A C) (f'1 ;; g'1))).
        * apply (QuotPrecategory_comp_iscontr_PAS p p').
      + apply idpath.
    - intros y.
      apply impred. intros t.
      apply impred. intros H.
      apply impred. intros t0.
      apply impred. intros H0.
      apply isasetsetquot.
    - intros y T. cbn in T.
      set (T' := T f'1 f''1 g'1 g''1). rewrite <- T'. apply idpath.
  Defined.
  Opaque QuotPrecategory_comp_iscontr.

  Definition QuotPrecategory_comp {A B C : ob PA} (f : QuotPrecategory_ob_mor⟦A, B⟧)
             (g : QuotPrecategory_ob_mor⟦B, C⟧) : QuotPrecategory_ob_mor⟦A, C⟧.
  Proof.
    exact (pr1 (pr1 (QuotPrecategory_comp_iscontr f g))).
  Defined.

  Definition to_quot_mor {x y : ob PA} (f : PA⟦x, y⟧) : QuotPrecategory_ob_mor⟦x, y⟧.
  Proof.
    use setquotpr. exact f.
  Defined.


  (** ** Some equations on linearity, compositions, and binops *)

  Lemma QuotPrecategory_comp_linear {x y z : ob PA} (f : PA⟦x, y⟧) (g : PA⟦y, z⟧) :
    QuotPrecategory_comp (to_quot_mor f) (to_quot_mor g) = to_quot_mor (f ;; g).
  Proof.
    unfold to_quot_mor. unfold QuotPrecategory_comp.
    apply pathsinv0.
    use (pr2 (pr1 (QuotPrecategory_comp_iscontr
                           (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) f)
                           (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) g)))).
    - apply idpath.
    - apply idpath.
  Qed.

  (** Pre- and postcomposition respect binop. *)
  Local Lemma QuotPrecategory_premor {x y z : PA} (f : PA⟦x, y⟧) (g h : PA⟦y, z⟧) :
    QuotPrecategory_comp (to_quot_mor f) ((to_quot_mor g * to_quot_mor h)%multmonoid) =
    ((QuotPrecategory_comp (to_quot_mor f) (to_quot_mor g)) *
     (QuotPrecategory_comp (to_quot_mor f) (to_quot_mor h)))%multmonoid.
  Proof.
    Opaque binopeqrel_subgr_eqrel isabgrquot setquotfun2.
    apply pathsinv0. cbn.
    eapply pathscomp0.
    - rewrite QuotPrecategory_comp_linear. rewrite QuotPrecategory_comp_linear.
      use setquotfun2comm.
    - apply pathsinv0.
      unfold to_quot_mor.
      set (tmp := setquotfun2comm (binopeqrel_subgr_eqrel (PAS y z))
                                  (binopeqrel_subgr_eqrel (PAS y z))
                                  (to_binop y z)
                                  (iscompbinoptransrel
                                     (binopeqrel_subgr_eqrel (PAS y z))
                                     (eqreltrans (binopeqrel_subgr_eqrel (PAS y z)))
                                     (pr2 (binopeqrel_subgr_eqrel (PAS y z))))).
      rewrite tmp. clear tmp.
      rewrite <- to_premor_linear'.
      apply pathsinv0.
      unfold QuotPrecategory_comp.
      apply (pr2 (pr1 (QuotPrecategory_comp_iscontr
                         (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) f)
                         (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) (to_binop y z g h))))).
      + apply idpath.
      + apply idpath.
  Qed.

  Local Lemma QuotPrecategory_postmor {x y z : PA} (f : PA⟦y, z⟧) (g h : PA⟦x, y⟧) :
    QuotPrecategory_comp (to_quot_mor g * to_quot_mor h)%multmonoid (to_quot_mor f) =
    ((QuotPrecategory_comp (to_quot_mor g) (to_quot_mor f)) *
     (QuotPrecategory_comp (to_quot_mor h) (to_quot_mor f)))%multmonoid.
  Proof.
    apply pathsinv0. cbn.
    eapply pathscomp0.
    - rewrite QuotPrecategory_comp_linear. rewrite QuotPrecategory_comp_linear.
      use setquotfun2comm.
    - unfold to_quot_mor. rewrite setquotfun2comm.
      unfold QuotPrecategory_comp.
      rewrite <- to_postmor_linear'.
      apply (pr2 (pr1 (QuotPrecategory_comp_iscontr
                         (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) (to_binop x y g h))
                         (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) f)))).
      + apply idpath.
      + apply idpath.
  Qed.

  (** Composing with the unit element gives the unit element. *)
  Local Lemma quot_comp_unel_left {x y z : PA} (f : PA⟦x, y⟧) :
    QuotPrecategory_comp (to_quot_mor f) (to_quot_mor (to_unel y z)) = (to_quot_mor (to_unel x z)).
  Proof.
    rewrite <- (to_premor_unel' _ _ f). unfold to_quot_mor. apply pathsinv0.
    unfold QuotPrecategory_comp.
    apply (pr2 (pr1 (QuotPrecategory_comp_iscontr
                       (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) f)
                       (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) (to_unel y z))))).
    - apply idpath.
    - apply idpath.
  Qed.

  Local Lemma quot_comp_unel_right {x y z : PA} (f : PA⟦y, z⟧) :
    QuotPrecategory_comp (to_quot_mor (to_unel x y)) (to_quot_mor f) =
    (to_quot_mor (to_unel x z)).
  Proof.
    rewrite <- (to_postmor_unel' _ _ f). unfold to_quot_mor. apply pathsinv0.
    unfold QuotPrecategory_comp.
    apply (pr2 (pr1 (QuotPrecategory_comp_iscontr
                       (setquotpr (binopeqrel_subgr_eqrel (PAS x y)) (to_unel x y))
                       (setquotpr (binopeqrel_subgr_eqrel (PAS y z)) f)))).
    - apply idpath.
    - apply idpath.
  Qed.


  (** ** Construction of the QuotPrecategory *)

  Definition QuotPrecategory_data : precategory_data :=
    precategory_data_pair
      QuotPrecategory_ob_mor (fun (A : ob PA) => setquotpr _ (identity A) )
      (fun (A B C : ob PA) (f : QuotPrecategory_ob_mor⟦A, B⟧)
         (g : QuotPrecategory_ob_mor⟦B, C⟧) => QuotPrecategory_comp f g).

  (** The following two lemmas are used to show associaticity of composition in
      QuotPrecategory. *)
  Lemma assoc1 {a b c d : QuotPrecategory_data} (f : QuotPrecategory_data ⟦a, b⟧)
        (g : QuotPrecategory_data ⟦b, c⟧) (h : QuotPrecategory_data ⟦c, d⟧)
        (f1 : PA⟦a, b⟧) (f2 : setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1 = f)
        (g1 : PA⟦b, c⟧) (g2 : setquotpr (binopeqrel_subgr_eqrel (PAS b c)) g1 = g)
        (h1 : PA⟦c, d⟧) (h2 : setquotpr (binopeqrel_subgr_eqrel (PAS c d)) h1 = h) :
    QuotPrecategory_comp f (QuotPrecategory_comp g h) =
    setquotpr (binopeqrel_subgr_eqrel (PAS a d)) (f1 ;; (g1 ;; h1)).
  Proof.
    apply pathsinv0.
    set (ic2 := QuotPrecategory_comp_iscontr g h).
    set (ic3 := QuotPrecategory_comp_iscontr f (pr1 (pr1 ic2))).
    set (tmp := pr2 (pr1 ic3)). cbn beta in tmp. unfold QuotPrecategory_comp.
    fold ic2. fold ic3. use tmp.
    - exact f2.
    - use (pr2 (pr1 ic2)).
      + exact g2.
      + exact h2.
  Qed.

  Lemma assoc2 {a b c d : QuotPrecategory_data} (f : QuotPrecategory_data ⟦a, b⟧)
        (g : QuotPrecategory_data ⟦b, c⟧) (h : QuotPrecategory_data ⟦c, d⟧)
        (f1 : PA⟦a, b⟧) (f2 : setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1 = f)
        (g1 : PA⟦b, c⟧) (g2 : setquotpr (binopeqrel_subgr_eqrel (PAS b c)) g1 = g)
        (h1 : PA⟦c, d⟧) (h2 : setquotpr (binopeqrel_subgr_eqrel (PAS c d)) h1 = h) :
    setquotpr (binopeqrel_subgr_eqrel (PAS a d)) ((f1 ;; g1) ;; h1) =
    QuotPrecategory_comp (QuotPrecategory_comp f g) h.
  Proof.
    set (ic1 := QuotPrecategory_comp_iscontr f g).
    set (ic4 := QuotPrecategory_comp_iscontr (pr1 (pr1 ic1)) h).
    set (tmp := pr2 (pr1 ic4)). cbn beta in tmp. unfold QuotPrecategory_comp.
    fold ic1. fold ic4. use tmp.
    - use (pr2 (pr1 ic1)).
      + exact f2.
      + exact g2.
    - exact h2.
  Qed.

  (** QuotPrecategory is a precategory *)
  Lemma is_precategory_QuotPrecategory_data : is_precategory QuotPrecategory_data.
  Proof.
    split.
    - split.
      (* id left *)
      + intros a b f. apply pathsinv0. cbn. unfold QuotPrecategory_comp.
        set (f'' := @issurjsetquotpr (to_abgrop a b) (binopeqrel_subgr_eqrel (PAS a b)) f).
        use (squash_to_prop f''). apply isasetsetquot. intros f'. clear f''.
        induction f' as [f1 f2]. rewrite <- f2. cbn in f1, a, b.
        eapply pathscomp0.
        * apply maponpaths. exact (! (id_left f1)).
        * apply (pr2 (pr1 (QuotPrecategory_comp_iscontr
                             (setquotpr (binopeqrel_subgr_eqrel (PAS a a)) (@identity PA a))
                             (setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1)))).
          -- apply idpath.
          -- apply idpath.
      (* id right *)
      + intros a b f. apply pathsinv0. cbn. unfold QuotPrecategory_comp.
        set (f'' := @issurjsetquotpr (to_abgrop a b) (binopeqrel_subgr_eqrel (PAS a b)) f).
        use (squash_to_prop f''). apply isasetsetquot. intros f'. clear f''.
        induction f' as [f1 f2]. rewrite <- f2. cbn in f1, a, b.
        eapply pathscomp0.
        * apply maponpaths. exact (! (id_right f1)).
        * apply (pr2 (pr1 (QuotPrecategory_comp_iscontr
                             (setquotpr (binopeqrel_subgr_eqrel (PAS a b)) f1)
                             (setquotpr (binopeqrel_subgr_eqrel (PAS b b)) (@identity PA b))))).
          -- apply idpath.
          -- apply idpath.
    (* assoc *)
    - intros a b c d f g h. cbn.
      set (f'' := @issurjsetquotpr (to_abgrop a b) (binopeqrel_subgr_eqrel (PAS a b)) f).
      use (squash_to_prop f''). apply isasetsetquot. intros f'. clear f''.
      set (g'' := @issurjsetquotpr (to_abgrop b c) (binopeqrel_subgr_eqrel (PAS b c)) g).
      use (squash_to_prop g''). apply isasetsetquot. intros g'. clear g''.
      set (h'' := @issurjsetquotpr (to_abgrop c d) (binopeqrel_subgr_eqrel (PAS c d)) h).
      use (squash_to_prop h''). apply isasetsetquot. intros h'. clear h''.
      induction f' as [f1 f2]. induction g' as [g1 g2]. induction h' as [h1 h2].
      cbn in f1, g1, h1.
      rewrite (assoc1 f g h f1 f2 g1 g2 h1 h2).
      rewrite <- (assoc2 f g h f1 f2 g1 g2 h1 h2).
      rewrite assoc. apply idpath.
  Qed.

  Definition QuotPrecategory : precategory :=
    tpair _ _ is_precategory_QuotPrecategory_data.

  Lemma has_homsets_QuotPrecategory : has_homsets QuotPrecategory.
  Proof.
    intros a b. apply isasetsetquot.
  Qed.


  (** ** Quotient precategory of PreAdditive is PreAdditive *)

  Opaque isbinopeqrel_subgr_eqrel isabgrquot.
  Definition QuotPrecategory_binops : PrecategoryWithBinOps.
  Proof.
    use mk_PrecategoryWithBinOps.
    - exact QuotPrecategory.
    - intros x y. exact (@op (subabgr_quot (PAS x y))).
  Defined.

  Local Lemma QuotPrecategory_isabgrops (x y : QuotPrecategory_binops) :
    @isabgrop
      (hSetpair (@setquot (PA ⟦ x, y ⟧) (@binopeqrel_subgr_eqrel (@to_abgrop PA x y) (PAS x y)))
                (has_homsets_QuotPrecategory x y))
      (@setquotfun2 (PA ⟦ x, y ⟧) (PA ⟦ x, y ⟧)
                    (@binopeqrel_subgr_eqrel (@to_abgrop PA x y) (PAS x y))
                    (@binopeqrel_subgr_eqrel (@to_abgrop PA x y) (PAS x y)) (@to_binop PA x y)
                    (@iscompbinoptransrel
                       (@to_setwithbinoppair PA x y)
                       (@binopeqrel_subgr_eqrel (@to_abgrop PA x y) (PAS x y))
                       (@eqreltrans (PA ⟦ x, y ⟧)
                                    (@binopeqrel_subgr_eqrel (@to_abgrop PA x y) (PAS x y)))
                       (@pr2 (eqrel (PA ⟦ x, y ⟧))
                             (λ R : eqrel (PA ⟦ x, y ⟧),
                                    @isbinophrel (@to_setwithbinoppair PA x y) R)
                             (@binopeqrel_subgr_eqrel (@to_abgrop PA x y) (PAS x y))))).
  Proof.
    exact (pr2 (subabgr_quot (PAS x y))).
  Defined.
  Opaque QuotPrecategory_isabgrops.
  (* isabgrops contains construction the unel of the homset. Thus this opaque might be problematic
     later. Use Transparent QuotPrecategory_isabgrops if needed. *)

  Definition QuotPrecategory_abgrops : PrecategoryWithAbgrops.
  Proof.
    use mk_PrecategoryWithAbgrops.
    - exact QuotPrecategory_binops.
    - exact has_homsets_QuotPrecategory.
    - intros x y. exact (QuotPrecategory_isabgrops x y).
  Defined.

  (** Don't know why we need unel and unel'. Try to fix this if you can. *)
  Local Lemma quot_unel (x y : PA) :
    @to_unel QuotPrecategory_abgrops x y = to_quot_mor (@to_unel PA x y).
  Proof.
    unfold to_unel. unfold to_quot_mor. apply pathsinv0. apply idpath.
  Qed.

  Local Lemma quot_unel' (x y : PA) : @to_unel QuotPrecategory_abgrops x y = 1%multmonoid.
  Proof.
    unfold to_unel.
    apply idpath.
  Qed.

  Local Lemma PreAdditive_pre_linear (x y z : PA) (f : setquot (binopeqrel_subgr_eqrel (PAS x y))) :
    isbinopfun (@to_premor QuotPrecategory_abgrops x y z f).
  Proof.
    set (f'1 := @issurjsetquotpr (to_abgrop x y) (binopeqrel_subgr_eqrel (PAS x y)) f).
    use (squash_to_prop f'1). apply isapropisbinopfun. intros f1. clear f'1.
    intros g h. cbn in g, h. cbn.
    set (g'1 := @issurjsetquotpr (to_abgrop y z) (binopeqrel_subgr_eqrel (PAS y z)) g).
    use (squash_to_prop g'1). apply has_homsets_QuotPrecategory. intros g1. clear g'1.
    set (h'1 := @issurjsetquotpr (to_abgrop y z) (binopeqrel_subgr_eqrel (PAS y z)) h).
    use (squash_to_prop h'1). apply has_homsets_QuotPrecategory. intros h1. clear h'1.
    induction f1 as [f1 f2]. induction g1 as [g1 g2]. induction h1 as [h1 h2].
    unfold to_premor. rewrite <- f2. rewrite <- g2. rewrite <- h2.
    set (tmp := QuotPrecategory_premor f1 g1 h1). unfold to_quot_mor in tmp. cbn.
    exact tmp.
  Qed.

  Local Lemma PreAdditive_pre_unel (x y z : PA) (f : setquot (binopeqrel_subgr_eqrel (PAS x y))) :
    @to_premor QuotPrecategory_abgrops x y z f 1%multmonoid = 1%multmonoid.
  Proof.
    cbn. rewrite <- quot_unel'. rewrite <- quot_unel'. rewrite quot_unel. rewrite quot_unel.
    set (f'1 := @issurjsetquotpr (to_abgrop x y) (binopeqrel_subgr_eqrel (PAS x y)) f).
    use (squash_to_prop f'1). apply has_homsets_QuotPrecategory. intros f1. clear f'1.
    induction f1 as [f1 f2].
    unfold to_premor. cbn. unfold QuotPrecategory_comp.
    set (tmp := @quot_comp_unel_left x y z f1). unfold to_quot_mor in tmp.
    unfold QuotPrecategory_comp in tmp. rewrite <- f2. unfold to_quot_mor.
    exact tmp.
  Qed.

  Local Lemma PreAdditive_post_linear (x y z : PA)
        (f : setquot (binopeqrel_subgr_eqrel (PAS y z))) :
    isbinopfun (@to_postmor QuotPrecategory_abgrops x y z f).
  Proof.
    set (f'1 := @issurjsetquotpr (to_abgrop y z) (binopeqrel_subgr_eqrel (PAS y z)) f).
    use (squash_to_prop f'1). apply isapropisbinopfun. intros f1. clear f'1.
    intros g h. cbn in g, h. cbn.
    set (g'1 := @issurjsetquotpr (to_abgrop x y) (binopeqrel_subgr_eqrel (PAS x y)) g).
    use (squash_to_prop g'1). apply has_homsets_QuotPrecategory. intros g1. clear g'1.
    set (h'1 := @issurjsetquotpr (to_abgrop x y) (binopeqrel_subgr_eqrel (PAS x y)) h).
    use (squash_to_prop h'1). apply has_homsets_QuotPrecategory. intros h1. clear h'1.
    induction f1 as [f1 f2]. induction g1 as [g1 g2]. induction h1 as [h1 h2].
    unfold to_postmor. rewrite <- f2. rewrite <- g2. rewrite <- h2.
    set (tmp := QuotPrecategory_postmor f1 g1 h1). unfold to_quot_mor in tmp. cbn.
    exact tmp.
  Qed.

  Local Lemma PreAdditive_post_unel (x y z : PA) (f : setquot (binopeqrel_subgr_eqrel (PAS y z))) :
    @to_postmor QuotPrecategory_abgrops x y z f 1%multmonoid = 1%multmonoid.
  Proof.
    cbn. rewrite <- quot_unel'. rewrite <- quot_unel'. rewrite quot_unel. rewrite quot_unel.
    set (f'1 := @issurjsetquotpr (to_abgrop y z) (binopeqrel_subgr_eqrel (PAS y z)) f).
    use (squash_to_prop f'1). apply has_homsets_QuotPrecategory. intros f1. clear f'1.
    induction f1 as [f1 f2].
    unfold to_postmor. cbn. unfold QuotPrecategory_comp.
    set (tmp := @quot_comp_unel_right x y z f1). unfold to_quot_mor in tmp.
    unfold QuotPrecategory_comp in tmp. rewrite <- f2. unfold to_quot_mor.
    exact tmp.
  Qed.

  Definition QuotPrecategory_PreAdditive : PreAdditive.
  Proof.
    use mk_PreAdditive.
    - exact QuotPrecategory_abgrops.
    - split.
      + intros x y z f. cbn in f, x, y, z.
        split.
        * exact (PreAdditive_pre_linear x y z f).
        * exact (PreAdditive_pre_unel x y z f).
      + intros x y z f. cbn in f, x, y, z.
        split.
        * exact (PreAdditive_post_linear x y z f).
        * exact (PreAdditive_post_unel x y z f).
  Defined.

  Lemma setquotpr_linear {x y : PA} (f g : PA⟦x, y⟧) :
    to_quot_mor (@to_binop PA _ _ f g) =
    @to_binop QuotPrecategory_PreAdditive _ _ (to_quot_mor f) (to_quot_mor g).
  Proof.
    set (tmp := pr1 (abgrquotpr_ismonoidfun (binopeqrel_subgr_eqrel (PAS x y))) f g).
    cbn beta in tmp. unfold to_quot_mor. apply tmp.
  Qed.

  Lemma comp_eq {x y z : PA} (f : QuotPrecategory_PreAdditive⟦x, y⟧)
        (g : QuotPrecategory_PreAdditive⟦y, z⟧) : QuotPrecategory_comp f g = f ;; g.
  Proof.
    apply idpath.
  Qed.


  (** ** If PA has a zero object, then so does QuotPrecategory of PA *)

  Variable Z : Zero PA.

  Lemma QuotPrecategory_isZero : isZero QuotPrecategory Z.
  Proof.
    use mk_isZero.
    - intros a.
      use tpair.
      + exact (to_quot_mor (@ZeroArrowFrom PA Z a)).
      + cbn beta. intros t.
        set (t'1 := @issurjsetquotpr (to_abgrop Z a) (binopeqrel_subgr_eqrel (PAS Z a)) t).
        use (squash_to_prop t'1). apply has_homsets_QuotPrecategory. intros t1. clear t'1.
        induction t1 as [t1 t2]. rewrite <- t2. unfold to_quot_mor. apply maponpaths.
        apply ArrowsFromZero.
    - intros a.
      use tpair.
      + exact (to_quot_mor (@ZeroArrowTo PA Z a)).
      + cbn beta. intros t.
        set (t'1 := @issurjsetquotpr (to_abgrop a Z) (binopeqrel_subgr_eqrel (PAS a Z)) t).
        use (squash_to_prop t'1). apply has_homsets_QuotPrecategory. intros t1. clear t'1.
        induction t1 as [t1 t2]. rewrite <- t2. unfold to_quot_mor. apply maponpaths.
        apply ArrowsToZero.
  Defined.
  Opaque QuotPrecategory_isZero.

  Definition QuotPrecategory_Zero : @Zero QuotPrecategory.
  Proof.
    use mk_Zero.
    - exact Z.
    - exact QuotPrecategory_isZero.
  Defined.

End preadditive_quotient.
