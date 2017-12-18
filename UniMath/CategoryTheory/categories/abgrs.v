(** * Category of abelian groups *)
(** ** Contents
- Precategory of abelian groups
- Category of abelian groups
- Zero object and Zero arrow
 - Zero object
 - Zero arrow
- Category of abelian groups is preadditive
- Category of abelian groups is additive
- Kernels and Cokernels
 - Kernels
 - Cokernels
- Monics are inclusions and Epis are surjections
 - Epis are surjections
 - Monics are inclusions
- Monics are kernels of their cokernels and epis are cokernels of their kernels
 - Monics are Kernels
 - Epis are Cokernels
- The category of abelian groups is an abelian category
- Corollaries to additive categories
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
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

Local Open Scope cat.


(** * Precategory of abelian groups
  - Objects are abelian groups, [abgr].
  - Morphisms are monoidfuns, [monoidfun].
*)
Section def_abgr_precategory.

  (** ** precategory_data *)

  Definition abgr_fun_space (A B : abgr) : hSet := hSetpair (monoidfun A B) (isasetmonoidfun A B).

  Definition abgr_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) abgr (λ A B : abgr, abgr_fun_space A B).

  Definition abgr_precategory_data : precategory_data :=
    precategory_data_pair
      abgr_precategory_ob_mor (λ (A : abgr), ((idmonoidiso A) : monoidfun A A))
      (fun (A B C : abgr) (f : monoidfun A B) (g : monoidfun B C) => monoidfuncomp f g).

  (** ** is_precategory *)

  Lemma is_precategory_abgr_precategory_data : is_precategory abgr_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use monoidfunidleft.
    - intros a b f. use monoidfunidright.
    - intros a b c d f g h. use monoidfunassoc.
  Qed.

  (** ** precategory and category *)

  Definition abgr_precategory : precategory :=
    mk_precategory abgr_precategory_data is_precategory_abgr_precategory_data.

  Lemma has_homsets_abgr : has_homsets abgr_precategory.
  Proof.
    intros a b. use isasetmonoidfun.
  Qed.

  Definition abgr_category : category := category_pair abgr_precategory has_homsets_abgr.

End def_abgr_precategory.


(** * Category of abelian groups
  - (monoidiso X Y) ≃ (iso X Y)
  - Category of abelian groups
*)
Section def_abgr_category.

  (** ** (monoidiso X Y) ≃ (iso X Y) *)

  Lemma abgr_iso_is_equiv (A B : ob abgr_category) (f : iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    use gradth.
    - exact (pr1monoidfun _ _ (inv_from_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_inv_after_iso f)) x).
      intros x0. use isapropismonoidfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_after_iso_inv f)) x).
      intros x0. use isapropismonoidfun.
  Qed.

  Lemma abgr_iso_equiv (X Y : ob abgr_category) : iso X Y -> monoidiso (X : abgr) (Y : abgr).
  Proof.
    intro f.
    use monoidisopair.
    - exact (weqpair (pr1 (pr1 f)) (abgr_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma abgr_equiv_is_iso (X Y : ob abgr_category) (f : monoidiso (X : abgr) (Y : abgr)) :
    @is_iso abgr_category X Y (monoidfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (monoidfunconstr (pr2 (invmonoidiso f))).
    - use mk_is_inverse_in_precat.
      + use monoidfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use monoidfun_paths. use funextfun. intros y. use homotweqinvweq.
  Qed.

  Definition abgr_equiv_iso (X Y : ob abgr_category) (f : monoidiso (X : abgr) (Y : abgr)) :
    iso X Y := @isopair abgr_category X Y (monoidfunconstr (pr2 f)) (abgr_equiv_is_iso X Y f).

  Lemma abgr_iso_equiv_is_equiv (X Y : abgr_category) : isweq (abgr_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (abgr_equiv_iso X Y).
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Qed.

  Definition abgr_iso_equiv_weq (X Y : ob abgr_category) :
    weq (iso X Y) (monoidiso (X : abgr) (Y : abgr)).
  Proof.
    use weqpair.
    - exact (abgr_iso_equiv X Y).
    - exact (abgr_iso_equiv_is_equiv X Y).
  Defined.

  Lemma abgr_equiv_iso_is_equiv (X Y : ob abgr_category) : isweq (abgr_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (abgr_iso_equiv X Y).
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
  Qed.

  Definition abgr_equiv_iso_weq (X Y : ob abgr_category) :
    (monoidiso (X : abgr) (Y : abgr)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (abgr_equiv_iso X Y).
    - exact (abgr_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of abelian groups *)

  Definition abgr_category_isweq (a b : ob abgr_category) : isweq (λ p : a = b, idtoiso p).
  Proof.
    use (@isweqhomot
           (a = b) (iso a b)
           (pr1weq (weqcomp (abgr_univalence a b) (abgr_equiv_iso_weq a b)))
           _ _ (weqproperty (weqcomp (abgr_univalence a b) (abgr_equiv_iso_weq a b)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use total2_paths_f.
      + use idpath.
      + use proofirrelevance. use isapropismonoidfun.
    - use proofirrelevance. use isaprop_is_iso.
  Qed.

  Definition abgr_category_is_univalent : is_univalent abgr_category.
  Proof.
    use dirprodpair.
    - intros a b. exact (abgr_category_isweq a b).
    - exact has_homsets_abgr.
  Defined.

  Definition abgr_univalent_category : univalent_category :=
    mk_category abgr_category abgr_category_is_univalent.

End def_abgr_category.


(** * Zero object and Zero arrow
   - Zero object is the abelian group which consists of one element, the unit element.
   - The unique morphism to zero object maps every element to the unit element.
   - The unique morphism from the zero object maps unit to unit.
   - The unique morphisms which factors through zero object maps every element to the unit
     element.
   - Computations on zero object
 *)
Section def_abgr_zero.

  (** ** Zero in abelian category *)

  Lemma isconnectedfromunitabgr (a : abgr_category) (t : abgr_category ⟦unitabgr, a⟧):
    (t : monoidfun unitabgr (a : abgr)) = abgrfunfromunit (a : abgr).
  Proof.
    use monoidfun_paths. use funextfun. intros x.
    use (pathscomp0 _ (monoidfununel t)). use maponpaths. use isProofIrrelevantUnit.
  Qed.

  Lemma isconnectedtounitabgr (a : abgr_category) (t : abgr_category ⟦a, unitabgr⟧):
    (t : monoidfun (a : abgr) unitabgr) = abgrfuntounit a.
  Proof.
    use monoidfun_paths. use funextfun. intros x. use isProofIrrelevantUnit.
  Qed.

  Definition abgr_isZero : isZero abgr_category unitabgr.
  Proof.
    use mk_isZero.
    - intros a. use iscontrpair.
      + exact (abgrfunfromunit a).
      + intros t. exact (isconnectedfromunitabgr a t).
    - intros a. use iscontrpair.
      + exact (abgrfuntounit a).
      + intros t. exact (isconnectedtounitabgr a t).
  Defined.

  Definition abgr_Zero : Zero abgr_category := @mk_Zero abgr_category unitabgr abgr_isZero.


  (** ** Computations on zero object *)

  Lemma abgr_Zero_comp : ZeroObject (abgr_Zero) = unitabgr.
  Proof.
    use idpath.
  Qed.

  Lemma abgr_Zero_from_comp (A : abgr) :
    @ZeroArrowFrom abgr_category abgr_Zero A = abgrfunfromunit A.
  Proof.
    use idpath.
  Qed.

  Lemma abgr_Zero_to_comp (A : abgr) :
    @ZeroArrowTo abgr_category abgr_Zero A = abgrfuntounit A.
  Proof.
    use idpath.
  Qed.

  Lemma abgr_Zero_arrow_comp (A B : abgr) :
    @ZeroArrow abgr_category abgr_Zero A B = unelabgrfun A B.
  Proof.
    use monoidfun_paths. use funextfun. intros x. use idpath.
  Qed.

End def_abgr_zero.


(** * Preadditive structure on the category of abelian groups
   - Binary operation on homsets.
   - Abelian group structure on homsets
   - PreAdditive structure on the category of abelian groups
*)
Section abgr_preadditive.

  (** ** Binary operations on homsets
      Let f, g : X --> Y be morphisms in the category of abelian groups. Then f + g is defined to be
      the morphism (f + g) x = (f x) + (g x). This gives [precategoryWithBinOps] structure on the
      category.
  *)

  Definition abgr_WithBinOpsData : precategoryWithBinOpsData abgr_category.
  Proof.
    intros X Y. exact (@abmonoidshombinop (X : abgr) (Y : abgr)).
  Defined.

  Definition abgr_WithBinOps : precategoryWithBinOps :=
    mk_precategoryWithBinOps abgr_category abgr_WithBinOpsData.

  (** ** [categoryWithAbgrops] structure on the category of abelian groups *)

  Definition abgr_WithAbGrops : categoryWithAbgrops.
  Proof.
    use mk_categoryWithAbgrops.
    - exact abgr_WithBinOps.
    - use homset_property.
    - use mk_categoryWithAbgropsData.
      intros X Y. exact (@abgrshomabgr_isabgrop X Y).
  Defined.

  (** ** [PreAdditive] structure on the category of abelian groups *)

  Definition abgr_isPreAdditive : isPreAdditive abgr_WithAbGrops.
  Proof.
    use mk_isPreAdditive.
    (* Precomposition with morphism is linear *)
    - intros X Y Z f.
      use mk_ismonoidfun.
      + use mk_isbinopfun. intros g h. use monoidfun_paths. use funextfun. intros x. use idpath.
      + use monoidfun_paths. use funextfun. intros x. use idpath.
    (* Postcomposition with morphism is linear *)
    - intros X Y Z f.
      use mk_ismonoidfun.
      + use mk_isbinopfun. intros g h. use monoidfun_paths. use funextfun. intros x.
        use (pathscomp0 ((pr1 (pr2 f)) _ _)). use idpath.
      + use monoidfun_paths. use funextfun. intros x. exact (monoidfununel f).
  Qed.

  Definition abgr_PreAdditive : PreAdditive :=
    mk_PreAdditive abgr_WithAbGrops abgr_isPreAdditive.

End abgr_preadditive.


(** * Additive structure on the category of abelian groups
   - Direct sums
   - Additive category structure
 *)
Section abgr_additive.

  (** ** Direct sums
     Direct sum of X and Y is given by the direct product abelian group X × Y. The inclusions
     and projections are given by
     - In1 :  x ↦ (x, 0)
     - In2 :  y ↦ (0, y)
     - Pr1 :  (x, y) ↦ x
     - Pr2 :  (x, y) ↦ y
   *)

  Lemma abgr_DirectSumPr1_ismonoidfun (A B : abgr) :
    ismonoidfun (λ X : abgrdirprod A B, dirprod_pr1 X).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'. use idpath.
    - use idpath.
  Qed.

  Definition abgr_DirectSumPr1 (A B : abgr) : abgr_category⟦abgrdirprod A B, A⟧ :=
    monoidfunconstr (abgr_DirectSumPr1_ismonoidfun A B).

  Lemma abgr_DirectSumPr2_ismonoidfun (A B : abgr) :
    ismonoidfun (λ X : abgrdirprod A B, dirprod_pr2 X).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'. use idpath.
    - use idpath.
  Qed.

  Definition abgr_DirectSumPr2 (A B : abgr) : abgr_category⟦abgrdirprod A B, B⟧ :=
    monoidfunconstr (abgr_DirectSumPr2_ismonoidfun A B).

  Lemma abgr_DirectSumIn1_ismonoidfun (A B : abgr) :
    @ismonoidfun A (abgrdirprod A B) (λ a : A, dirprodpair a (unel B)).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'. use dirprod_paths.
      + use idpath.
      + use pathsinv0. use (runax B).
    - use dirprod_paths.
      + use idpath.
      + use idpath.
  Qed.

  Definition abgr_DirectSumIn1 (A B : abgr) : abgr_category⟦A, abgrdirprod A B⟧ :=
    monoidfunconstr (abgr_DirectSumIn1_ismonoidfun A B).

  Lemma abgr_DirectSumIn2_ismonoidfun (A B : abgr) :
    @ismonoidfun B (abgrdirprod A B) (λ b : B, dirprodpair (unel A) b).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'. use dirprod_paths.
      + use pathsinv0. use (runax A).
      + use idpath.
    - use dirprod_paths.
      + use idpath.
      + use idpath.
  Qed.

  Definition abgr_DirectSumIn2 (A B : abgr) : abgr_category⟦B, abgrdirprod A B⟧ :=
    monoidfunconstr (abgr_DirectSumIn2_ismonoidfun A B).

  Lemma abgr_DirectSumIdIn1 (A B : abgr) :
    abgr_DirectSumIn1 A B · abgr_DirectSumPr1 A B = (idmonoidiso A : monoidfun A A).
  Proof.
    use monoidfun_paths. use funextfun. intros x. use idpath.
  Qed.

  Lemma abgr_DirectSumIdIn2 (A B : abgr) :
    abgr_DirectSumIn2 A B · abgr_DirectSumPr2 A B = (idmonoidiso B : monoidfun B B).
  Proof.
    use monoidfun_paths. use funextfun. intros x. use idpath.
  Qed.

  Lemma abgr_DirectSumUnel1 (A B : abgr) :
    abgr_DirectSumIn1 A B · abgr_DirectSumPr2 A B = @to_unel abgr_PreAdditive A B.
  Proof.
    use monoidfun_paths. use funextfun. intros x. use idpath.
  Qed.

  Lemma abgr_DirectSumUnel2 (A B : abgr) :
    abgr_DirectSumIn2 A B · abgr_DirectSumPr1 A B = @to_unel abgr_PreAdditive B A.
  Proof.
    use monoidfun_paths. use funextfun. intros x. use idpath.
  Qed.

  Lemma abgr_DirectSumId (A B : abgr) :
    @abmonoidshombinop
      (abgrdirprod A B) (abgrdirprod A B)
      (abgr_DirectSumPr1 A B · abgr_DirectSumIn1 A B)
      (abgr_DirectSumPr2 A B · abgr_DirectSumIn2 A B) =
    ((idmonoidiso (abgrdirprod A B)) : monoidfun (abgrdirprod A B) (abgrdirprod A B)) .
  Proof.
    use monoidfun_paths. use funextfun. intros x. use dirprod_paths.
    - use (runax A).
    - use (lunax B).
  Qed.

  Lemma abgr_isBinCoproduct_Comm1 {X Y Z : abgr}
        (f : abgr_PreAdditive ⟦X, Z⟧) (g : abgr_PreAdditive ⟦Y, Z⟧) :
    (monoidfuncomp (abgr_DirectSumIn1 X Y)
                   (@abmonoidshombinop
                      (abgrdirprod X Y) Z
                      (monoidfuncomp (abgr_DirectSumPr1 X Y) f)
                      (monoidfuncomp (abgr_DirectSumPr2 X Y) g)) = f)
      × (monoidfuncomp (abgr_DirectSumIn2 X Y)
                       (@abmonoidshombinop
                          (abgrdirprod X Y) Z
                          (monoidfuncomp (abgr_DirectSumPr1 X Y) f)
                          (monoidfuncomp (abgr_DirectSumPr2 X Y) g)) = g).
  Proof.
    use dirprodpair.
    - use monoidfun_paths. use funextfun. intros x.
      use (pathscomp0
             (maponpaths (λ z : (Z : abgr), (pr1 f x * z)%multmonoid) (monoidfununel g))).
      use (runax (Z : abgr)).
    - use monoidfun_paths. use funextfun. intros y.
      use (pathscomp0
             (maponpaths (λ z : (Z : abgr), (z * pr1 g y)%multmonoid) (monoidfununel f))).
      use (lunax (Z : abgr)).
  Qed.

  Lemma abgr_isBinCoproduct_Path1 {X Y Z : abgr}
        (f : abgr_PreAdditive ⟦X, Z⟧) (g : abgr_PreAdditive ⟦Y, Z⟧)
        (t1 : abgr_PreAdditive ⟦abgrdirprod X Y, Z⟧)
        (H1 : abgr_DirectSumIn1 X Y · t1 = f) (H2 : abgr_DirectSumIn2 X Y · t1 = g) :
    t1 = @abmonoidshombinop
           (abgrdirprod X Y) Z
           (monoidfuncomp (abgr_DirectSumPr1 X Y) f)
           (monoidfuncomp (abgr_DirectSumPr2 X Y) g).
  Proof.
    use monoidfun_paths. use pathscomp0.
    - exact (pr1 (@abmonoidshombinop
                    (abgrdirprod X Y) Z
                    ((abgr_DirectSumPr1 X Y) · abgr_DirectSumIn1 X Y · t1)
                    ((abgr_DirectSumPr2 X Y) · abgr_DirectSumIn2 X Y · t1))).
    - use funextfun. intros x. induction x as [x1 x2].
      use (pathscomp0 _ (binopfunisbinopfun
                           (t1 : monoidfun (abgrdirprod X Y) (Z : abgr))
                           (@dirprodpair X Y x1 (unel Y)) (@dirprodpair X Y (unel X) x2))).
      use maponpaths. use dirprod_paths.
      + use pathsinv0. use (runax X).
      + use pathsinv0. use (lunax Y).
    - cbn. rewrite <- H1. rewrite <- H2.
      use funextfun. intros x. use idpath.
  Qed.

  Lemma abgr_isBinCoproduct_Pair {X Y Z : abgr} (f : monoidfun X Z) (g : monoidfun Y Z) :
    ∑ (k : abgr_PreAdditive ⟦abgrdirprod X Y, Z⟧),
    (abgr_DirectSumIn1 X Y · k = f) × (abgr_DirectSumIn2 X Y · k = g).
  Proof.
    use tpair.
    - exact (@abmonoidshombinop
               (abgrdirprod X Y) Z (abgr_DirectSumPr1 X Y · f) (abgr_DirectSumPr2 X Y · g)).
    - exact (abgr_isBinCoproduct_Comm1 f g).
  Defined.

  Lemma abgr_isBinCoproduct_Uniqueness {X Y Z : abgr} (f : monoidfun X Z) (g : monoidfun Y Z)
        (t : ∑ (k : abgr_PreAdditive ⟦abgrdirprod X Y, Z⟧),
             (abgr_DirectSumIn1 X Y · k = f) × (abgr_DirectSumIn2 X Y · k = g)) :
    t = abgr_isBinCoproduct_Pair f g.
  Proof.
    use total2_paths_f.
    - exact (abgr_isBinCoproduct_Path1
               f g (pr1 t) (dirprod_pr1 (pr2 t)) (dirprod_pr2 (pr2 t))).
    - use proofirrelevance. use isapropdirprod.
      + use setproperty.
      + use setproperty.
  Qed.

  Lemma abgr_isBinCoproduct (X Y : abgr) :
    isBinCoproduct
      abgr_PreAdditive X Y (abgrdirprod X Y) (abgr_DirectSumIn1 X Y) (abgr_DirectSumIn2 X Y).
  Proof.
    use mk_isBinCoproduct.
    - use homset_property.
    - intros Z f g. use iscontrpair.
      + exact (abgr_isBinCoproduct_Pair f g).
      + intros t. exact (abgr_isBinCoproduct_Uniqueness f g t).
  Defined.

  Lemma abgr_isBinProduct_Comm1 {X Y Z : abgr} (f : abgr_PreAdditive ⟦Z, X⟧)
        (g : abgr_PreAdditive ⟦Z, Y⟧) :
    (monoidfuncomp
       (@abmonoidshombinop
          Z (abgrdirprod X Y)
          (monoidfuncomp f (abgr_DirectSumIn1 X Y)) (monoidfuncomp g (abgr_DirectSumIn2 X Y)))
       (abgr_DirectSumPr1 X Y) = f)
      × (monoidfuncomp
           (@abmonoidshombinop
              Z (abgrdirprod X Y)
              (monoidfuncomp f (abgr_DirectSumIn1 X Y)) (monoidfuncomp g (abgr_DirectSumIn2 X Y)))
           (abgr_DirectSumPr2 X Y) = g).
  Proof.
    use dirprodpair.
    - use monoidfun_paths. use funextfun. intros z. use (runax X).
    - use monoidfun_paths. use funextfun. intros z. use (lunax Y).
  Qed.

  Lemma abgr_isBinProduct_Paths1 {X Y Z : abgr} (f : abgr_PreAdditive ⟦Z, X⟧)
        (g : abgr_PreAdditive ⟦Z, Y⟧) (t : abgr_PreAdditive ⟦Z, abgrdirprod X Y⟧)
        (H1 : t · abgr_DirectSumPr1 X Y = f) (H2 : t · abgr_DirectSumPr2 X Y = g) :
    t = @abmonoidshombinop
          Z (abgrdirprod X Y)
          (monoidfuncomp f (abgr_DirectSumIn1 X Y))
          (monoidfuncomp g (abgr_DirectSumIn2 X Y)).
  Proof.
    use monoidfun_paths. use pathscomp0.
    - exact (pr1 (@abmonoidshombinop
                    Z (abgrdirprod X Y)
                    (t · (abgr_DirectSumPr1 X Y) · abgr_DirectSumIn1 X Y)
                    (t · (abgr_DirectSumPr2 X Y) · abgr_DirectSumIn2 X Y))).
    - use funextfun. intros z. use dirprod_paths.
      + use pathsinv0. use (runax X).
      + use pathsinv0. use (lunax Y).
    - cbn. rewrite <- H1. rewrite <- H2. use funextfun. intros z. use idpath.
  Qed.

  Definition abgr_isBinProduct_Pair {X Y Z : abgr} (f : abgr_category⟦Z, X⟧)
             (g : abgr_category⟦Z, Y⟧) :
    ∑ (k : abgr_PreAdditive ⟦Z, abgrdirprod X Y⟧),
    (k · abgr_DirectSumPr1 X Y = f) × (k · abgr_DirectSumPr2 X Y = g).
  Proof.
    use tpair.
    - exact (@abmonoidshombinop
               Z (abgrdirprod X Y) (f · abgr_DirectSumIn1 X Y) (g · abgr_DirectSumIn2 X Y)).
    - exact (abgr_isBinProduct_Comm1 f g).
  Defined.

  Lemma abgr_isBinProduct_Uniqueness {X Y Z : abgr} (f : abgr_category⟦Z, X⟧)
        (g : abgr_category⟦Z, Y⟧)
        (t : ∑ k : abgr_PreAdditive ⟦ Z, abgrdirprod X Y ⟧,
                   k · abgr_DirectSumPr1 X Y = f × k · abgr_DirectSumPr2 X Y = g) :
    t = abgr_isBinProduct_Pair f g.
  Proof.
    use total2_paths_f.
    - exact (abgr_isBinProduct_Paths1
               f g (pr1 t) (dirprod_pr1 (pr2 t)) (dirprod_pr2 (pr2 t))).
    - use proofirrelevance. use isapropdirprod.
      + use setproperty.
      + use setproperty.
  Qed.

  Lemma abgr_isBinProduct (X Y : abgr) :
    isBinProduct
      abgr_PreAdditive X Y (abgrdirprod X Y) (abgr_DirectSumPr1 X Y) (abgr_DirectSumPr2 X Y).
  Proof.
    use mk_isBinProduct.
    - use homset_property.
    - intros Z f g. use iscontrpair.
      + exact (abgr_isBinProduct_Pair f g).
      + intros t. exact (abgr_isBinProduct_Uniqueness f g t).
  Defined.

  Lemma abgr_isBinDirectSum (X Y : abgr) :
    isBinDirectSum
      abgr_PreAdditive X Y (abgrdirprod X Y) (abgr_DirectSumIn1 X Y) (abgr_DirectSumIn2 X Y)
      (abgr_DirectSumPr1 X Y) (abgr_DirectSumPr2 X Y).
  Proof.
    use mk_isBinDirectSum.
    - exact (abgr_isBinCoproduct X Y).
    - exact (abgr_isBinProduct X Y).
    - exact (abgr_DirectSumIdIn1 X Y).
    - exact (abgr_DirectSumIdIn2 X Y).
    - exact (abgr_DirectSumUnel1 X Y).
    - exact (abgr_DirectSumUnel2 X Y).
    - exact (abgr_DirectSumId X Y).
  Defined.

  Definition abgr_isAdditive : isAdditive abgr_PreAdditive.
  Proof.
    use mk_isAdditive.
    - exact abgr_Zero.
    - use mk_BinDirectSums. intros X Y. use mk_BinDirectSum.
      + exact (abgrdirprod X Y).
      + exact (abgr_DirectSumIn1 X Y).
      + exact (abgr_DirectSumIn2 X Y).
      + exact (abgr_DirectSumPr1 X Y).
      + exact (abgr_DirectSumPr2 X Y).
      + exact (abgr_isBinDirectSum X Y).
  Defined.

  Definition abgr_Additive : Additive := mk_Additive abgr_PreAdditive abgr_isAdditive.

End abgr_additive.


(** * Kernels and Cokernels
   - Kernels in the category of abelian groups
   - Cokernels in the category of abelian groups
 *)
Section abgr_kernels_and_cokernels.

  Definition abgr_kernel_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtype A :=
    (λ x : A, ishinh ((f x) = unel B)).

  Definition abgr_image_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtype B :=
    (λ y : B, ∃ x : A, (f x) = y).

  (** ** Kernels
      Let f : X -> Y be a morphism of abelian groups. A kernel of f is given by the subgroup of X
      consisting of elements x such that [f x = unel Y].
   *)

  (** *** Kernel as abelian group *)

  Definition abgr_Kernel_subabgr_issubgr {A B : abgr} (f : monoidfun A B) :
    issubgr (abgr_kernel_hsubtype f).
  Proof.
    use issubgrpair.
    - use issubmonoidpair.
      + intros a a'.
        use (hinhuniv _ (pr2 a)). intros ae.
        use (hinhuniv _ (pr2 a')). intros a'e.
        use hinhpr.
        use (pathscomp0 (binopfunisbinopfun f (pr1 a) (pr1 a'))).
        rewrite ae. rewrite a'e. use (runax B).
      + use hinhpr. exact (monoidfununel f).
    - intros x a.
      use (hinhuniv _ a). intros ae.
      use hinhpr.
      use (grrcan B (f x)).
      use (pathscomp0 (! (binopfunisbinopfun f (grinv A x) x))).
      use (pathscomp0 (maponpaths (λ a : A, f a) (grlinvax A x))).
      use (pathscomp0 (monoidfununel f)).
      use pathsinv0. use (pathscomp0 (lunax B (f x))). exact ae.
  Qed.

  Definition abgr_Kernel_subabgr {A B : abgr} (f : monoidfun A B) : @subabgr A :=
    subgrconstr (@abgr_kernel_hsubtype A B f) (abgr_Kernel_subabgr_issubgr f).

  (** *** The inclusion Kernel f --> X is a morphism of abelian groups *)

  Definition abgr_Kernel_monoidfun_ismonoidfun {A B : abgr} (f : monoidfun A B) :
    @ismonoidfun (abgr_Kernel_subabgr f) A
                 (inclpair (pr1carrier (abgr_kernel_hsubtype f))
                           (isinclpr1carrier (abgr_kernel_hsubtype f))).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'. use idpath.
    - use idpath.
  Qed.

  Definition abgr_Kernel_monoidfun {A B : abgr} (f : monoidfun A B) :
    abgr_category⟦carrierofasubabgr (abgr_Kernel_subabgr f), A⟧ :=
    monoidincltomonoidfun
      (abgr_Kernel_subabgr f) A
      (@monoidmonopair (abgr_Kernel_subabgr f) A
                       (inclpair (pr1carrier (abgr_kernel_hsubtype f))
                                 (isinclpr1carrier (abgr_kernel_hsubtype f)))
                       (abgr_Kernel_monoidfun_ismonoidfun f)).

  (** *** Composition Kernel f --> X --> Y is the zero arrow *)

  Definition abgr_Kernel_eq {A B : abgr} (f : monoidfun A B) :
    abgr_Kernel_monoidfun f · f = ZeroArrow abgr_Zero (carrierofasubabgr (abgr_Kernel_subabgr f)) B.
  Proof.
    use monoidfun_paths. use funextfun. intros x.
    use (squash_to_prop (pr2 x) (setproperty B _ _)).
    intros H. exact H.
  Qed.

  (** *** KernelIn morphism *)

  Lemma abgr_KernelArrowIn_map_property {A B C : abgr_category} (h : C --> A) (f : A --> B)
             (H : h · f = ZeroArrow abgr_Zero C B) (c : (C : abgr)) :
    ishinh_UU (pr1 f (pr1 h c) = 1%multmonoid).
  Proof.
    use hinhpr. use (pathscomp0 (toforallpaths _ _ _ (base_paths _ _ H) c)). use idpath.
  Qed.

  Definition abgr_KernelArrowIn_map {A B C : abgr_category} (h : C --> A) (f : A --> B)
             (H : h · f = ZeroArrow abgr_Zero C B) (c : (C : abgr)) : abgr_Kernel_subabgr f.
  Proof.
    use tpair.
    - exact (pr1 h c).
    - exact (abgr_KernelArrowIn_map_property h f H c).
  Defined.

  Lemma abgr_KernelArrowIn_ismonoidfun {A B C : abgr_category} (h : C --> A)
        (f : A --> B) (H : h · f = ZeroArrow abgr_Zero C B) :
    @ismonoidfun (C : abgr) (@abgr_Kernel_subabgr A B f) (@abgr_KernelArrowIn_map A B C h f H).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'. use total2_paths_f.
      + exact (binopfunisbinopfun (h : monoidfun (C : abgr) (A : abgr)) x x').
      + use proofirrelevance. use propproperty.
    - use total2_paths_f.
      + exact (monoidfununel h).
      + use proofirrelevance. use propproperty.
  Qed.

  Definition abgr_KernelArrowIn {A B C : abgr_category} (h : C --> A) (f : A --> B)
             (H : h · f = ZeroArrow abgr_Zero C B) :
    abgr_category⟦C, carrierofasubabgr (abgr_Kernel_subabgr f)⟧.
  Proof.
    use monoidfunconstr.
    - exact (abgr_KernelArrowIn_map h f H).
    - exact (abgr_KernelArrowIn_ismonoidfun h f H).
  Defined.

  (** *** Kernels *)

  Definition abgr_Kernel_isKernel_KernelArrrow {A B C : abgr} (f : abgr_category ⟦A, B⟧)
             (h : abgr_category ⟦C, A⟧) (H' : h · f = ZeroArrow abgr_Zero C B) :
    ∑ ψ : abgr_category ⟦C, carrierofasubabgr (abgr_Kernel_subabgr f)⟧,
          ψ · abgr_Kernel_monoidfun f = h.
  Proof.
    use tpair.
    - exact (abgr_KernelArrowIn h f H').
    - use monoidfun_paths. use funextfun. intros x. use idpath.
  Defined.

  Definition abgr_Kernel_isKernel_uniqueness {A B C : abgr} (f : abgr_category ⟦A, B⟧)
             (h : abgr_category ⟦C, A⟧) (H' : h · f = ZeroArrow abgr_Zero C B)
             (t : ∑ (t1 : abgr_category ⟦C, carrierofasubabgr (abgr_Kernel_subabgr f)⟧),
                  t1 · abgr_Kernel_monoidfun f = h) :
    t = abgr_Kernel_isKernel_KernelArrrow f h H'.
  Proof.
    use total2_paths_f.
    - use monoidfun_paths. use funextfun. intros x. use total2_paths_f.
      + exact (toforallpaths _ _ _ (base_paths _ _ (pr2 t)) x).
      + use proofirrelevance. use propproperty.
    - use proofirrelevance. use setproperty.
  Qed.

  Definition abgr_Kernel_isKernel {A B : abgr} (f : abgr_category⟦A, B⟧) :
    isKernel abgr_Zero (abgr_Kernel_monoidfun f) f (abgr_Kernel_eq f).
  Proof.
    use mk_isKernel.
    - use homset_property.
    - intros w h H'.
      use iscontrpair.
      + exact (abgr_Kernel_isKernel_KernelArrrow f h H').
      + intros t. exact (abgr_Kernel_isKernel_uniqueness f h H' t).
  Defined.

  Definition abgr_Kernel {A B : abgr} (f : monoidfun A B) :
    Kernel abgr_Zero f :=
    mk_Kernel (abgr_Zero) (abgr_Kernel_monoidfun f) f (abgr_Kernel_eq f) (abgr_Kernel_isKernel f).

  Corollary abgr_Kernels : Kernels abgr_Zero.
  Proof.
    intros A B f. exact (abgr_Kernel f).
  Defined.


  (** ** Cokernels
     - Let f : X --> Y be a morphism of abelian groups. A cokernel for f is given by the quotient
       quotient group Y/(Im f) together with the canonical morphism Y --> Y/(Im f).
   *)

  (** *** Image of f is a subgroup *)

  Definition abgr_image_issubgr {A B : abgr} (f : monoidfun A B) : issubgr (abgr_image_hsubtype f).
  Proof.
    use issubgrpair.
    - use issubmonoidpair.
      + intros a a'.
        use (hinhuniv _ (pr2 a)). intros ae.
        use (hinhuniv _ (pr2 a')). intros a'e.
        use hinhpr.
        use tpair.
        * exact (@op A (pr1 ae) (pr1 a'e)).
        * use (pathscomp0 (binopfunisbinopfun f (pr1 ae) (pr1 a'e))).
          use two_arg_paths.
          -- exact (pr2 ae).
          -- exact (pr2 a'e).
      + use hinhpr. use tpair.
        * exact (unel A).
        * exact (monoidfununel f).
    - intros b b'.
      use (hinhuniv _ b'). intros eb.
      use hinhpr.
      use tpair.
      + exact (grinv A (pr1 eb)).
      + use (pathscomp0 _ (maponpaths (λ bb : B, (grinv B bb)) (pr2 eb))).
        use monoidfuninvtoinv.
  Qed.

  Definition abgr_image {A B : abgr} (f : monoidfun A B) : @subabgr B :=
    @subgrconstr B (@abgr_image_hsubtype A B f) (abgr_image_issubgr f).

  (** *** Subgroup gives an equivalence relation. *)

  Definition abgr_Cokernel_eqrel_istrans {A B : abgr} (f : monoidfun A B) :
    istrans (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 x2 x3 y1 y2.
    use (hinhuniv _ y1). intros y1'.
    use (hinhuniv _ y2). intros y2'.
    use hinhpr.
    use tpair.
    - exact (@op A (pr1 y1') (pr1 y2')).
    - use (pathscomp0 (binopfunisbinopfun f (pr1 y1') (pr1 y2'))).
      rewrite (pr2 y1'). rewrite (pr2 y2').
      rewrite <- assocax. rewrite (assocax _ _ _ x2). rewrite (grlinvax B). rewrite (runax B).
      use idpath.
  Qed.

  Definition abgr_Cokernel_eqrel_isrefl {A B : abgr} (f : monoidfun A B) :
    isrefl (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 P X. use X. clear P X.
    use tpair.
    - exact (unel A).
    - cbn. rewrite (grrinvax B). use (monoidfununel f).
  Qed.

  Definition abgr_Cokernel_eqrel_issymm {A B : abgr} (f : monoidfun A B) :
    issymm (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 x2 x3.
    use (hinhuniv _ x3). intros x3'.
    intros P X. use X. clear P X.
    use tpair.
    - exact (grinv A (pr1 x3')).
    - use (pathscomp0 (monoidfuninvtoinv f (pr1 x3'))).
      rewrite (pr2 x3'). rewrite grinvop. use two_arg_paths.
      + use grinvinv.
      + use idpath.
  Qed.

  Definition abgr_Cokernel_eqrel {A B : abgr} (f : monoidfun A B) : eqrel B :=
    @eqrelconstr B (λ b1 : B, λ b2 : B, ∃ a : A, (f a) = (op b1 (grinv B b2)))
                 (abgr_Cokernel_eqrel_istrans f) (abgr_Cokernel_eqrel_isrefl f)
                 (abgr_Cokernel_eqrel_issymm f).

  (** *** Construction of the quotient abelian group Y/(Im f) *)

  Definition abgr_Cokernel_abgr_isbinoprel {A B : abgr} (f : monoidfun A B) :
    isbinophrel (λ b1 b2 : pr1 B, ∃ a : pr1 A, pr1 f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    use isbinophrelif.
    - exact (commax B).
    - intros x1 x2 x3 y1. use (hinhuniv _ y1). intros y1'. use hinhpr.
      use tpair.
      + exact (pr1 y1').
      + use (pathscomp0 (pr2 y1')). rewrite grinvop.
        rewrite (commax B x3). rewrite (assocax B). rewrite (commax B x3).
        rewrite (assocax B). rewrite (grlinvax B x3). rewrite (runax B). use idpath.
  Qed.

  Definition abgr_Cokernel_abgr {A B : abgr} (f : monoidfun A B) : abgr :=
    @abgrquot B (binopeqrelpair (abgr_Cokernel_eqrel f) (abgr_Cokernel_abgr_isbinoprel f)).

  (** *** The canonical morphism Y --> Y/(Im f) *)

  Lemma abgr_CokernelArrow_ismonoidfun {A B : abgr} (f : monoidfun A B) :
    @ismonoidfun B (@abgr_Cokernel_abgr A B f) (@setquotpr B (@abgr_Cokernel_eqrel A B f)).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'. use idpath.
    - use idpath.
  Qed.

  Definition abgr_CokernelArrow {A B : abgr} (f : monoidfun A B) :
    abgr_category⟦B, abgr_Cokernel_abgr f⟧.
  Proof.
    use monoidfunconstr.
    - exact (setquotpr (abgr_Cokernel_eqrel f)).
    - exact (abgr_CokernelArrow_ismonoidfun f).
  Defined.

  (** *** CokernelOut *)

  Lemma abgr_Cokernel_monoidfun_issurjective {A B : abgr} (f : monoidfun A B) :
    issurjective (pr1 (abgr_CokernelArrow f)).
  Proof.
    use issurjsetquotpr.
  Qed.

  Definition abgr_Cokernel_eq {A B : abgr} (f : abgr_category⟦A, B⟧) :
    f · abgr_CokernelArrow f = ZeroArrow abgr_Zero A (abgr_Cokernel_abgr f).
  Proof.
    use monoidfun_paths. use funextfun. intros a.
    use (iscompsetquotpr (abgr_Cokernel_eqrel f)).
    use hinhpr.
    use tpair.
    - exact a.
    - use (pathscomp0 (pathsinv0 (runax B (pr1 f a)))).
      use two_arg_paths.
      + use idpath.
      + use pathsinv0. use (grinvunel B).
  Qed.

  Definition abgr_CokernelArrowOutUniv_iscomprelfun {A B C : abgr_category}
             (f : A --> B) (h : B --> C) (H : f · h = ZeroArrow abgr_Zero A C) :
    iscomprelfun (λ b1 b2 : pr1 B, ∃ a : pr1 A, pr1 f a = (b1 * grinv (abgrtogr B) b2)%multmonoid)
                 (pr1 h).
  Proof.
    intros x x' X.
    use (squash_to_prop X (setproperty (C : abgr) (pr1 h x) (pr1 h x'))). intros X'.
    use (grrcan (abgrtogr C) ((pr1 h) (grinv (abgrtogr B) x'))).
    use (pathscomp0 _ (binopfunisbinopfun
                         (h : monoidfun (B : abgr) (C : abgr)) x' (grinv (B : abgr) x'))).
    use (pathscomp0 _ (! maponpaths (λ xx : (B : abgr), pr1 h xx) (grrinvax (B : abgr) x'))).
    use (pathscomp0 _ (! (monoidfununel h))).
    use (pathscomp0 _ (toforallpaths _ _ _ (base_paths _ _ H) (pr1 X'))).
    use (pathscomp0 (! (binopfunisbinopfun
                          (h : monoidfun (B : abgr) (C : abgr)) x (grinv (B : abgr) x')))).
    use maponpaths. use pathsinv0. exact (pr2 X').
  Qed.

  Definition abgr_CokernelOut_map {A B C : abgr_category} (f : A --> B)
             (h : B --> C) (H : f · h = ZeroArrow abgr_Zero A C) :
    (abgr_Cokernel_abgr f) -> (pr1 C) :=
    setquotuniv (λ b1 b2 : pr1 B, ∃ a : pr1 A, pr1 f a = (b1 * grinv (abgrtogr B) b2)%multmonoid)
                (pr1 C) (pr1 h) (abgr_CokernelArrowOutUniv_iscomprelfun f h H).

  Definition abgr_CokernelOut_ismonoidfun {A B C : abgr} (f : abgr_category ⟦A, B⟧)
             (h : abgr_category ⟦B, C⟧) (H : f · h = ZeroArrow abgr_Zero A C) :
    @ismonoidfun (@abgr_Cokernel_abgr A B f) C (@abgr_CokernelOut_map A B C f h H).
  Proof.
    use mk_ismonoidfun.
    - exact (@isbinopfun_twooutof3b
               (pr1 B) (abgr_Cokernel_abgr f) C
               (pr1 (abgr_CokernelArrow f))
               (abgr_CokernelOut_map f h H)
               (abgr_Cokernel_monoidfun_issurjective f)
               (binopfunisbinopfun (h : monoidfun B C))
               (binopfunisbinopfun ((abgr_CokernelArrow f) : monoidfun B _))).
    - exact (monoidfununel (h : monoidfun B C)).
  Qed.

  Definition abgr_CokernelOut {A B C : abgr} (f : abgr_category⟦A, B⟧) (h : abgr_category⟦B, C⟧)
             (H : f · h = ZeroArrow abgr_Zero A C) : monoidfun (abgr_Cokernel_abgr f) C :=
    monoidfunconstr (abgr_CokernelOut_ismonoidfun f h H).

  Lemma abgr_CokernelOut_Comm {A B C : abgr} (f : abgr_category⟦A, B⟧) (h : abgr_category⟦B, C⟧)
        (H : f · h = ZeroArrow abgr_Zero A C) :
    monoidfuncomp (abgr_CokernelArrow f) (abgr_CokernelOut f h H) = h.
  Proof.
    use monoidfun_paths. use funextfun. intros x. use idpath.
  Qed.

  Definition abgr_CokernelOut_pair {A B C : abgr} (f : abgr_category ⟦A, B⟧)
             (h : abgr_category ⟦B, C⟧) (H : f · h = ZeroArrow abgr_Zero A C) :
    ∑ ψ : abgr_category⟦abgr_Cokernel_abgr f, C⟧, abgr_CokernelArrow f · ψ = h.
  Proof.
    use tpair.
    - exact (abgr_CokernelOut f h H).
    - exact (abgr_CokernelOut_Comm f h H).
  Defined.

  (** *** Cokernels *)

  Lemma abgr_isCokernel_uniquenss {A B C : abgr} (f : abgr_category⟦A, B⟧) (h : abgr_category⟦B, C⟧)
        (H : f · h = ZeroArrow abgr_Zero A C)
        (t : ∑ ψ : abgr_category ⟦abgr_Cokernel_abgr f, C⟧, abgr_CokernelArrow f · ψ = h) :
    t = abgr_CokernelOut_pair f h H.
  Proof.
    use total2_paths_f.
    - use monoidfun_paths. use funextfun. intros x.
      use (squash_to_prop (abgr_Cokernel_monoidfun_issurjective f x) (setproperty C _ _)).
      intros hf. rewrite <- (hfiberpr2 _ _ hf).
      exact (toforallpaths _ _ _ (base_paths _ _ (pr2 t)) (hfiberpr1 _ _ hf)).
    - use proofirrelevance. use homset_property.
  Qed.

  Definition abgr_isCokernel {A B : abgr} (f : abgr_category⟦A, B⟧) :
    isCokernel abgr_Zero f (abgr_CokernelArrow f) (abgr_Cokernel_eq f).
  Proof.
    use mk_isCokernel.
    - use homset_property.
    - intros C h H. use iscontrpair.
      + exact (abgr_CokernelOut_pair f h H).
      + intros t. exact (abgr_isCokernel_uniquenss f h H t).
  Defined.

  Definition abgr_Cokernel {A B : abgr} (f : abgr_category⟦A, B⟧) : Cokernel abgr_Zero f :=
    mk_Cokernel abgr_Zero f (abgr_CokernelArrow f) (abgr_Cokernel_eq f) (abgr_isCokernel f).

  Corollary abgr_Cokernels : Cokernels abgr_Zero.
  Proof.
    intros A B f. exact (abgr_Cokernel f).
  Defined.

End abgr_kernels_and_cokernels.


(** * Monics are injective and epis are surjective
   - Epis are surjective
   - Monics are injective
*)
Section abgr_monics_and_epis.

  (** ** Epis *)

  Definition abgr_epi_hfiber_inhabited
             {A B : abgr} (f : abgr_category⟦A, B⟧) (isE : isEpi f) (b : B)
             (H : setquotpr (abgr_Cokernel_eqrel f) b =
                  setquotpr (abgr_Cokernel_eqrel f) 1%multmonoid) : ∥ hfiber (pr1 f) b ∥.
  Proof.
    set (tmp := weqpathsinsetquot (abgr_Cokernel_eqrel f) b (unel _)).
    use (hinhuniv _ ((invweq tmp) H)). intros Y. use hinhpr. induction Y as [t p].
    rewrite grinvunel in p. rewrite (runax B) in p.
    exact (hfiberpair (pr1 f) t p).
  Qed.

  Definition abgr_epi_issurjective {A B : abgr} (f : abgr_category⟦A, B⟧) (isE : isEpi f) :
    issurjective (pr1 f).
  Proof.
    intros x. use abgr_epi_hfiber_inhabited.
    - exact isE.
    - set (tmp := isE (abgr_Cokernel_abgr f) (abgr_CokernelArrow f)
                      (unelabgrfun B (abgr_Cokernel_abgr f))).
      assert (H : f · abgr_CokernelArrow f = f · unelabgrfun B (abgr_Cokernel_abgr f)).
      {
        rewrite abgr_Cokernel_eq.
        rewrite <- abgr_Zero_arrow_comp.
        rewrite ZeroArrow_comp_right.
        use idpath.
      }
      exact (toforallpaths _ _ _ (base_paths _ _ (tmp H)) x).
  Qed.


  (** ** Monics *)

  Lemma nat_nat_prod_abgr_monoidfun_paths {A B : abgr} (a1 a2 : A) (f : monoidfun A B)
        (H : f a1 = f a2) : monoidfuncomp (nat_nat_prod_abmonoid_monoidfun a1) f =
                            monoidfuncomp (nat_nat_prod_abmonoid_monoidfun a2) f.
  Proof.
    use monoidfun_paths. use funextfun. intros x. induction x as [x1 x2]. cbn.
    unfold funcomp. unfold nataddabmonoid_nataddabmonoid_to_monoid_fun.
    unfold nat_nat_to_monoid_fun. Opaque nat_to_monoid_fun. cbn.
    use (pathscomp0 (binopfunisbinopfun f _ _)).
    use (pathscomp0 _ (! (binopfunisbinopfun f _ _))). cbn.
    rewrite (monoidfun_nat_to_monoid_fun f a1 x1).
    rewrite (monoidfun_nat_to_monoid_fun f a2 x1).
    rewrite (monoidfun_nat_to_monoid_fun f (grinv A a1) x2).
    rewrite (monoidfun_nat_to_monoid_fun f (grinv A a2) x2).
    use two_arg_paths.
    - induction H. use idpath.
    - assert (e : f (grinv A a1) = f (grinv A a2)). {
        use (@grlcan B _ _ (pr1 f a1)).
        use (pathscomp0 (! binopfunisbinopfun f a1 (grinv A a1))).
        use (pathscomp0 (maponpaths (pr1 f) (grrinvax A a1))).
        cbn in H. rewrite H.
        use (pathscomp0 _ (binopfunisbinopfun f a2 (grinv A a2))).
        use (pathscomp0 _ (! (maponpaths (pr1 f) (grrinvax A a2)))).
        use idpath.
      }
      induction e. use idpath.
  Qed.
  Transparent nat_to_monoid_fun.

  Lemma abgr_monoidfun_precomp {A :abmonoid} {B C : abgr} (f1 f2 : monoidfun B C)
        (g : monoidfun A B) (H : issurjective (pr1 g)) :
    monoidfuncomp g f1 = monoidfuncomp g f2 -> f1 = f2.
  Proof.
    intros e. use monoidfun_paths. use funextfun. intros x.
    use (squash_to_prop (H x) (setproperty C _ _)). intros hf.
    rewrite <- (hfiberpr2 _ _ hf).
    exact (toforallpaths _ _ _ (base_paths _ _ e) (hfiberpr1 _ _ hf)).
  Qed.

  Lemma hz_abgr_fun_monoifun_paths {A B : abgr} (a1 a2 : A) (f : monoidfun A B) (H : f a1 = f a2) :
    monoidfuncomp (hz_abgr_fun_monoidfun a1) f = monoidfuncomp (hz_abgr_fun_monoidfun a2) f.
  Proof.
    use (@abgr_monoidfun_precomp
           (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig))
           hzaddabgr B
           (monoidfuncomp (hz_abgr_fun_monoidfun a1) f)
           (monoidfuncomp (hz_abgr_fun_monoidfun a2) f)
           hz_abmonoid_monoidfun).
    - use issurjsetquotpr.
    - rewrite monoidfunassoc. rewrite monoidfunassoc.
      rewrite abgr_natnat_hz_X_comm. rewrite abgr_natnat_hz_X_comm.
      exact (nat_nat_prod_abgr_monoidfun_paths a1 a2 f H).
  Qed.

  Definition abgr_monic_isincl {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f) :
    isincl (pr1 f).
  Proof.
    intros b h1 h2.
    use iscontrpair.
    - use total2_paths_f.
      + set (e := hfiberpr2 _ _ h1 @ (! hfiberpr2 _ _ h2)).
        set (tmp := isM hzaddabgr (hz_abgr_fun_monoidfun (pr1 h1))
                        (hz_abgr_fun_monoidfun (pr1 h2))
                        (hz_abgr_fun_monoifun_paths (pr1 h1) (pr1 h2) f e)).
        set (e' := toforallpaths _ _ _ (base_paths _ _ tmp) hzone).
        use (grrcan A (unel A)). use (grrcan A (unel A)). exact e'.
      + use proofirrelevance. use (setproperty B).
    - intros t. use proofirrelevance. use isaset_hfiber.
      + use setproperty.
      + use setproperty.
  Qed.

  Definition abgr_monic_isInjective {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f) :
    isInjective (pr1 f).
  Proof.
    exact (isweqonpathsincl (pr1 f) (abgr_monic_isincl f isM)).
  Qed.

  Lemma abgr_monic_paths {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f) (a1 a2 : A) :
    pr1 f a1 = pr1 f a2 -> a1 = a2.
  Proof.
    exact (invweq (weqpair _ (abgr_monic_isInjective f isM a1 a2))).
  Qed.

  Lemma abgr_monoidfun_postcomp {A B C : abgr} (f1 f2 : monoidfun A B) (g : monoidfun B C)
        (isM : isMonic (g : abgr_category⟦B, C⟧)) :
    monoidfuncomp f1 g = monoidfuncomp f2 g -> f1 = f2.
  Proof.
    intros e. use monoidfun_paths. use funextfun. intros x.
    use (invmap (weqpair _ (abgr_monic_isInjective g isM (pr1 f1 x) (pr1 f2 x)))).
    exact (toforallpaths _ _ _ (base_paths _ _ e) x).
  Qed.

End abgr_monics_and_epis.


(** * Monics are kernels of their cokernels and epis are cokernels of their kernels *)
Section abgr_monic_kernels_epi_cokernels.


  (** ** Monics are kernels of their cokernels *)

  Definition abgr_monic_kernel_in_hfiber_iscontr {A B C : abgr} (f : abgr_category⟦A, B⟧)
             (isM : isMonic f) (h : abgr_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) =
                  ZeroArrow abgr_Zero C (abgr_Cokernel f)) (c : C) :
    iscontr (hfiber (pr1 f) (pr1 h c)).
  Proof.
    use (squash_to_prop
           ((invweq (weqpathsinsetquot (abgr_Cokernel_eqrel f) (pr1 h c) (unel _)))
              (toforallpaths _ _ _ (base_paths _ _ H) c)) (isapropiscontr _)).
    intros hf.
    use iscontrpair.
    - use hfiberpair.
      + exact (pr1 hf).
      + use (pathscomp0 (pr2 hf)). rewrite grinvunel. use (runax B).
    - intros t. use total2_paths_f.
      + use (invmap (weqpair _ (abgr_monic_isInjective f isM (pr1 t) (pr1 hf)))).
        use (pathscomp0 (hfiberpr2 _ _ t)). use (pathscomp0 _ (! (pr2 hf))).
        rewrite grinvunel. rewrite runax. use idpath.
      + use proofirrelevance. use (setproperty B).
  Qed.

  Lemma abgr_monic_kernel_in_hfiber_mult_eq {A B : abgr} (f : abgr_category⟦A, B⟧)
        (w : abgr) (x x' : w) (h : abgr_category⟦w, B⟧) (X : hfiber (pr1 f) (pr1 h x))
        (X0 : hfiber (pr1 f) (pr1 h x')) :
    pr1 f (pr1 X * pr1 X0)%multmonoid = pr1 h (x * x')%multmonoid.
  Proof.
    rewrite (pr1 (pr2 f)).
    rewrite (pr2 X).
    rewrite (pr2 X0).
    rewrite (pr1 (pr2 h)).
    use idpath.
  Qed.

  Definition abgr_monic_kernel_in_hfiber_mult {A B : abgr} (f : abgr_category⟦A, B⟧)
             (w : abgr) (x x' : w) (h : abgr_category⟦w, B⟧) :
    hfiber (pr1 f) (pr1 h x) -> hfiber (pr1 f) (pr1 h x')
    -> hfiber (pr1 f) (pr1 h (x * x')%multmonoid).
  Proof.
    intros X X0.
    exact (hfiberpair (pr1 f) ((pr1 X) * (pr1 X0))%multmonoid
                      (abgr_monic_kernel_in_hfiber_mult_eq f w x x' h X X0)).
  Defined.

  Lemma abgr_monic_kernel_in_hfiber_unel_eq {A B C : abgr} (f : abgr_category⟦A, B⟧)
        (h : abgr_category⟦C, B⟧) : pr1 f 1%multmonoid = pr1 h 1%multmonoid.
  Proof.
    rewrite (pr2 (pr2 h)). use (pr2 (pr2 f)).
  Qed.

  Definition abgr_monic_kernel_in_hfiber_unel {A B : abgr} (f : abgr_category⟦A, B⟧) (w : abgr)
             (h : abgr_category⟦w, B⟧) : hfiber (pr1 f) (pr1 h 1%multmonoid) :=
    hfiberpair (pr1 f) 1%multmonoid (abgr_monic_kernel_in_hfiber_unel_eq f h).

  Definition abgr_monic_kernel_in {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f)
             (w : abgr) (h: abgr_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) : w -> A.
  Proof.
    intros x.
    exact (hfiberpr1 _ _ (iscontrpr1 (@abgr_monic_kernel_in_hfiber_iscontr A B w f isM h H x))).
  Defined.

  Definition abgr_monic_kernel_in_ismonoidfun {A B : abgr} (f : abgr_category⟦A, B⟧)
             (isM : isMonic f) (w : abgr) (h: abgr_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) :
    ismonoidfun (abgr_monic_kernel_in f isM w h H).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'.
      set (t := abgr_monic_kernel_in_hfiber_iscontr f isM h H x).
      set (tmp := abgr_monic_kernel_in_hfiber_mult
                    f w x x' h
                    (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x))
                    (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x'))).
      use pathscomp0.
      + exact (hfiberpr1 _ _ tmp).
      + unfold abgr_monic_kernel_in.
        use (invmap (weqpair _ (abgr_monic_isInjective f isM _ _))).
        use (pathscomp0 (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr
                                                      f isM h H (x * x')%multmonoid)))).
        use pathsinv0.
        exact (hfiberpr2 _ _ tmp).
      + use idpath.
    - assert (e : iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H 1%multmonoid)
                  = (abgr_monic_kernel_in_hfiber_unel f w h)).
      {
        use total2_paths_f.
        - use (invmap (weqpair _ (abgr_monic_isInjective f isM _ _))).
          use (pathscomp0 (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr
                                                        f isM h H 1%multmonoid)))).
          use pathsinv0.
          exact (hfiberpr2 _ _ (abgr_monic_kernel_in_hfiber_unel f w h)).
        - use proofirrelevance. use setproperty.
      }
      exact (base_paths _ _ e).
  Qed.

  Definition abgr_monic_kernel_in_monoidfun {A B : abgr} (f : abgr_category⟦A, B⟧)
             (isM : isMonic f) (w : abgr) (h: abgr_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) :
    monoidfun w A := monoidfunconstr (abgr_monic_kernel_in_ismonoidfun f isM w h H).

  Definition abgr_monic_Kernel_eq {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f) :
    f · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero A (abgr_Cokernel f).
  Proof.
    use CokernelCompZero.
  Qed.

  Lemma abgr_monic_Kernel_isKernel_comm {A B C : abgr} (f : abgr_category⟦A, B⟧)
        (isM : isMonic f) (h : abgr_category⟦C, B⟧)
        (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f)):
    monoidfuncomp (abgr_monic_kernel_in_monoidfun f isM C h H) f = h.
  Proof.
    use monoidfun_paths. use funextfun. intros x.
    exact (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x))).
  Qed.

  Definition abgr_monic_Kernel_isKernel_pair {A B C : abgr} (f : abgr_category⟦A, B⟧)
             (isM : isMonic f) (h : abgr_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f)) :
    ∑ ψ : abgr_category ⟦C, A⟧, ψ · f = h.
  Proof.
    use tpair.
    - exact (abgr_monic_kernel_in_monoidfun f isM C h H).
    - exact (abgr_monic_Kernel_isKernel_comm f isM h H).
  Defined.

  Definition abgr_monic_Kernel_isKernel_uniqueness {A B C : abgr} (f : abgr_category⟦A, B⟧)
             (isM : isMonic f) (h : abgr_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f))
             (t : ∑ ψ : abgr_category ⟦C, A⟧, ψ · f = h) :
    t = abgr_monic_Kernel_isKernel_pair f isM h H.
  Proof.
    use total2_paths_f.
    - use monoidfun_paths. use funextfun. intros x.
      use (invmap (weqpair _ (abgr_monic_isInjective f isM _ _))).
      use (pathscomp0 (toforallpaths _ _ _ (base_paths _ _ (pr2 t)) x)).
      use pathsinv0.
      exact (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x))).
    - use proofirrelevance. use setproperty.
  Qed.

  Definition abgr_monic_Kernel_isKernel {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f) :
    isKernel abgr_Zero f (CokernelArrow (abgr_Cokernel f))
             (CokernelCompZero abgr_Zero (abgr_Cokernel f)).
  Proof.
    use mk_isKernel.
    - use homset_property.
    - intros w h H.
      use iscontrpair.
      + exact (abgr_monic_Kernel_isKernel_pair f isM h H).
      + exact (abgr_monic_Kernel_isKernel_uniqueness f isM h H).
  Defined.

  Definition abgr_monic_kernel {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f) :
    Kernel abgr_Zero (CokernelArrow (abgr_Cokernel f)) :=
    mk_Kernel abgr_Zero f (CokernelArrow (abgr_Cokernel f)) (abgr_monic_Kernel_eq f isM)
              (abgr_monic_Kernel_isKernel f isM).

  Lemma abgr_monic_kernel_comp {A B : abgr} (f : abgr_category⟦A, B⟧) (isM : isMonic f) :
    KernelArrow (abgr_monic_kernel f isM) = f.
  Proof.
    use idpath.
  Qed.


  (** ** Epis are cokernels of their kernels *)

  Definition abgr_epi_cokernel_out_kernel_hsubtype {A B : abgr} (f : abgr_category⟦A, B⟧) (a : A)
             (H : pr1 f a = 1%multmonoid) : abgr_kernel_hsubtype f.
  Proof.
    use tpair.
    - exact a.
    - use hinhpr. exact H.
  Defined.

  Lemma abgr_epi_cokernel_out_data_eq {A B C : abgr} (f : abgr_category⟦A, B⟧)
        (isE : isEpi f) (h : abgr_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    ∏ x : abgr_kernel_hsubtype f, pr1 h (pr1carrier (abgr_kernel_hsubtype f) x) = 1%multmonoid.
  Proof.
    exact (toforallpaths _ _ _ (base_paths _ _ H)).
  Qed.

  Lemma abgr_epi_cokernel_out_data_hfibers_to_unel {A B : abgr} (f : abgr_category⟦A, B⟧) (b : B)
        (hfib1 hfib2 : hfiber (pr1 f) b) :
    (pr1 f) ((pr1 hfib1) * (grinv A (pr1 hfib2)))%multmonoid = unel B.
  Proof.
    rewrite (pr1 (pr2 f)).
    use (grrcan (abgrtogr B) (pr1 f (pr1 hfib2))).
    rewrite (assocax B). rewrite <- (pr1 (pr2 f)).
    rewrite (grlinvax A). rewrite (pr2 (pr2 f)).
    rewrite (runax B). rewrite (lunax B).
    rewrite (pr2 hfib1). rewrite (pr2 hfib2).
    use idpath.
  Qed.

  Lemma abgr_epi_cokernel_out_data_hfiber_eq {A B C : abgr} (f : abgr_category⟦A, B⟧)
        (isE : isEpi f) (h : abgr_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) (b : B)
        (X : hfiber (pr1 f) b) : ∏ hfib : hfiber (pr1 f) b, pr1 h (pr1 hfib) = pr1 h (pr1 X).
  Proof.
    intros hfib.
    use (grrcan C (grinv (abgrtogr C) (pr1 h (pr1 X)))).
    rewrite (grrinvax C).
    set (e1 := abgr_epi_cokernel_out_data_hfibers_to_unel f b hfib X).
    set (tmp1 := ! (monoidfuninvtoinv h (hfiberpr1 _ _ X))). cbn in tmp1.
    use (pathscomp0 (maponpaths (λ k : _, ((pr1 h (pr1 hfib)) * k)%multmonoid) tmp1)).
    rewrite <- (pr1 (pr2 h)).
    set (tmp2 := abgr_epi_cokernel_out_data_eq f isE h H).
    set (tmp3 := abgr_epi_cokernel_out_kernel_hsubtype
                   f (pr1 hfib * grinv A (pr1 X))%multmonoid e1).
    set (tmp4 := tmp2 tmp3). cbn in tmp4. exact tmp4.
  Qed.

  Lemma abgr_epi_CokernelOut_iscontr {A B C : abgr} (f : abgr_category⟦A, B⟧)
        (isE : isEpi f) (h : abgr_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) (b : B) :
    iscontr (∑ x : C, ∏ (hfib : hfiber (pr1 f) b), pr1 h (pr1 hfib) = x).
  Proof.
    use (squash_to_prop (abgr_epi_issurjective f isE b) (isapropiscontr _)).
    intros X. use iscontrpair.
    - use tpair.
      + exact (pr1 h (pr1 X)).
      + exact (abgr_epi_cokernel_out_data_hfiber_eq f isE h H b X).
    - intros t. use total2_paths_f.
      + exact (! ((pr2 t) X)).
      + use proofirrelevance. use impred. intros t0. use (setproperty C).
  Defined.

  Definition abgr_epi_CokernelOut_mult_eq {A B C : abgr} (b1 b2 : B)
             (f : abgr_category⟦A, B⟧) (isE : isEpi f) (h : abgr_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _)
             (X : ∑ x : C, ∏ hfib : hfiber (pr1 f) b1, pr1 h (pr1 hfib) = x)
             (X0 : ∑ x : C, ∏ hfib : hfiber (pr1 f) b2, pr1 h (pr1 hfib) = x) :
    ∏ hfib : hfiber (pr1 f) (b1 * b2)%multmonoid, pr1 h (pr1 hfib) = (pr1 X * pr1 X0)%multmonoid.
  Proof.
    intros hfib.
    use (squash_to_prop (abgr_epi_issurjective f isE b1) (setproperty C _ _)). intros X1.
    use (squash_to_prop (abgr_epi_issurjective f isE b2) (setproperty C _ _)). intros X2.
    rewrite <- ((pr2 X) X1). rewrite <- ((pr2 X0) X2). rewrite <- (pr1 (pr2 h)).
    exact (abgr_epi_cokernel_out_data_hfiber_eq
             f isE h H (b1 * b2)%multmonoid (hfiberbinop (f : monoidfun _ _) b1 b2 X1 X2) hfib).
  Qed.

  Definition abgr_epi_cokernel_out_data_mult {A B C : abgr} (b1 b2 : B)
             (f : abgr_category⟦A, B⟧) (isE : isEpi f) (h : abgr_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    (∑ x : C, ∏ (hfib : hfiber (pr1 f) b1), pr1 h (pr1 hfib) = x) ->
    (∑ x : C, ∏ (hfib : hfiber (pr1 f) b2), pr1 h (pr1 hfib) = x) ->
    (∑ x : C, ∏ (hfib : hfiber (pr1 f) (b1 * b2)%multmonoid), pr1 h (pr1 hfib) = x).
  Proof.
    intros X X0.
    exact (tpair _ ((pr1 X) * (pr1 X0))%multmonoid
                 (abgr_epi_CokernelOut_mult_eq b1 b2 f isE h H X X0)).
  Defined.

  Definition abgr_epi_cokernel_out_data_unel_eq {A B C : abgr}
             (f : abgr_category⟦A, B⟧) (isE : isEpi f) (h : abgr_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    ∏ hfib : hfiber (pr1 f) 1%multmonoid, pr1 h (pr1 hfib) = 1%multmonoid.
  Proof.
    intros hfib.
    set (hfib_unel := hfiberpair (pr1 f) 1%multmonoid (pr2 (pr2 f))).
    rewrite (abgr_epi_cokernel_out_data_hfiber_eq f isE h H 1%multmonoid hfib_unel hfib).
    exact (monoidfununel h).
  Qed.

  Definition abgr_epi_cokernel_out_data_unel {A B C : abgr} (f : abgr_category⟦A, B⟧)
             (isE : isEpi f) (h : abgr_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    ( ∑ x : C, ∏ (hfib : hfiber (pr1 f) 1%multmonoid),  pr1 h (pr1 hfib) = x) :=
    tpair _ 1%multmonoid (abgr_epi_cokernel_out_data_unel_eq f isE h H).

  Lemma abgr_epi_cokernel_out_ismonoidfun {A B C : abgr} (f : abgr_category⟦A, B⟧)
        (isE : isEpi f) (h : abgr_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    ismonoidfun (λ b : B, (pr1 (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H b)))).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x x'.
      set (HH0 := abgr_epi_cokernel_out_data_mult
                    x x' f isE h H
                    (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H x))
                    (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H x'))).
      assert (HH : iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H (x * x')%multmonoid) = HH0).
      {
        set (tmp := abgr_epi_CokernelOut_iscontr f isE h H (x * x')%multmonoid).
        rewrite (pr2 tmp). use pathsinv0. rewrite (pr2 tmp).
        use idpath.
      }
      exact (base_paths _ _ HH).
    - assert (HH : iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H 1%multmonoid)
                   = abgr_epi_cokernel_out_data_unel f isE h H).
      {
        rewrite (pr2 (abgr_epi_CokernelOut_iscontr f isE h H 1%multmonoid)).
        use pathsinv0.
        rewrite (pr2 (abgr_epi_CokernelOut_iscontr f isE h H 1%multmonoid)).
        use idpath.
      }
      exact (base_paths _ _ HH).
  Qed.

  Definition abgr_epi_cokernel_out_monoidfun {A B C : abgr} (f : abgr_category⟦A, B⟧)
             (isE : isEpi f) (h : abgr_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    monoidfun B C := monoidfunconstr (abgr_epi_cokernel_out_ismonoidfun f isE h H).

  Definition abgr_epi_cokernel_eq {A B : abgr} (f : abgr_category⟦A, B⟧) (isE : isEpi f) :
    KernelArrow (abgr_Kernel f) · f = ZeroArrow abgr_Zero _ _.
  Proof.
    use KernelCompZero.
  Qed.

  Lemma abgr_epi_cokernel_isCokernel_comm {A B C : abgr} (f : abgr_category⟦A, B⟧)
             (isE : isEpi f)  (h : abgr_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    f · abgr_epi_cokernel_out_monoidfun f isE h H = h.
  Proof.
    use total2_paths_f.
    - use funextfun. intros x. use pathsinv0.
      exact (pr2 (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H (pr1 f x)))
                 (@hfiberpair _ _ (pr1 f) (pr1 f x) x (idpath _))).
    - use proofirrelevance. use isapropismonoidfun.
  Qed.

  Definition abgr_epi_cokernel_isCokernel_pair {A B C : abgr} (f : abgr_category⟦A, B⟧)
             (isE : isEpi f)  (h : abgr_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    ∑ ψ : abgr_category ⟦B, C⟧, f · ψ = h.
  Proof.
    use tpair.
    - exact (abgr_epi_cokernel_out_monoidfun f isE h H).
    - exact (abgr_epi_cokernel_isCokernel_comm f isE h H).
  Defined.

  Lemma abgr_epi_cokernel_isCokernel_uniqueness {A B C : abgr} (f : abgr_category⟦A, B⟧)
        (isE : isEpi f)  (h : abgr_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C)
        (t : ∑ ψ : abgr_category ⟦B, C⟧, f · ψ = h) :
    t = abgr_epi_cokernel_isCokernel_pair f isE h H.
  Proof.
    use total2_paths_f.
    - use isE. use (pathscomp0 (pr2 t)). use monoidfun_paths. use funextfun. intros x.
      exact (pr2 (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H (pr1 f x)))
                 (@hfiberpair _ _ (pr1 f) (pr1 f x) x (idpath _))).
    - use proofirrelevance. use setproperty.
  Qed.

  Definition abgr_epi_cokernel_isCokernel {A B : abgr} (f : abgr_category⟦A, B⟧) (isE : isEpi f) :
    isCokernel abgr_Zero (KernelArrow (abgr_Kernel f)) f (abgr_epi_cokernel_eq f isE).
  Proof.
    use mk_isCokernel.
    - use homset_property.
    - intros w h H. use iscontrpair.
      + exact (abgr_epi_cokernel_isCokernel_pair f isE h H).
      + intros t. exact (abgr_epi_cokernel_isCokernel_uniqueness f isE h H t).
  Defined.

  Definition abgr_epi_cokernel {A B : abgr} (f : abgr_category⟦A, B⟧) (isE : isEpi f) :
    Cokernel abgr_Zero (KernelArrow (abgr_Kernel f)) :=
    mk_Cokernel abgr_Zero (KernelArrow (abgr_Kernel f)) f _ (abgr_epi_cokernel_isCokernel f isE).

  Definition abgr_epi_cokernel_comp {A B : abgr} (f : abgr_category⟦A, B⟧) (isE : isEpi f) :
    CokernelArrow (abgr_epi_cokernel f isE) = f.
  Proof.
    use idpath.
  Qed.

End abgr_monic_kernels_epi_cokernels.


(** * Category of abelian groups is an abelian category *)
Section abgr_abelian.

  Definition abgr_Abelian : AbelianPreCat.
  Proof.
    set (BinDS := to_BinDirectSums abgr_Additive).
    use (mk_Abelian abgr_category).
    - use mk_Data1.
      + exact abgr_Zero.
      + intros X Y. exact (BinDirectSum_BinProduct abgr_Additive (BinDS X Y)).
      + intros X Y. exact (BinDirectSum_BinCoproduct abgr_Additive (BinDS X Y)).
    - use mk_AbelianData.
      + use mk_Data2.
        * intros A B f. exact (abgr_Kernel f).
        * intros A B f. exact (abgr_Cokernel f).
      + use mk_MonicsAreKernels.
        intros x y M.
        exact (KernelisKernel abgr_Zero (abgr_monic_kernel M (MonicisMonic abgr_category M))).
      + use mk_EpisAreCokernels.
        intros x y E.
        exact (CokernelisCokernel abgr_Zero (abgr_epi_cokernel E (EpiisEpi abgr_category E))).
  Defined.

End abgr_abelian.


(** * Corollaries to additive categories
   In an additive category the homsets are abelian groups and pre- and postcompositions are
   morphisms of abelian groups. In this section we prove the following lemmas about additive
   categories using the theory of abelian groups developed above
   - A morphism φ in an additive category which gives isomorphisms (φ · _) and (_ · φ) is an
     isomorphism, [abgr_Additive_premor_postmor_is_iso].
   - A criteria of being a kernel in the category of abelian groups which uses only elements
     of abelian groups, [abgr_isKernel_Criteria].
*)
Section abgr_corollaries.

  (** ** Isomorphism criteria *)

  (** *** (_ · ZeroArrow) = ZeroArrow = (ZeroArrow · _) *)

  Lemma AdditiveZeroArrow_postmor_Abelian {Add : Additive} (x y z : Add) :
    to_postmor_monoidfun Add x y z (ZeroArrow (Additive.to_Zero Add) y z) =
    ZeroArrow (to_Zero abgr_Abelian) (@to_abgrop Add x y) (@to_abgrop Add x z).
  Proof.
    rewrite <- PreAdditive_unel_zero.
    use monoidfun_paths. use funextfun. intros f. exact (to_premor_unel Add z f).
  Qed.

  Lemma AdditiveZeroArrow_premor_Abelian {Add : Additive} (x y z : Add) :
    to_premor_monoidfun Add x y z (ZeroArrow (Additive.to_Zero Add) x y) =
    ZeroArrow (to_Zero abgr_Abelian) (@to_abgrop Add y z) (@to_abgrop Add x z).
  Proof.
    rewrite <- PreAdditive_unel_zero.
    use monoidfun_paths. use funextfun. intros f. exact (to_postmor_unel Add x f).
  Qed.

  (** *** f isomorphism ⇒ (f · _) isomorphism *)

  Local Lemma abgr_Additive_is_iso_premor_inverses {Add : Additive} (x y z : Add) {f : x --> y}
        (H : is_z_isomorphism f) :
    is_inverse_in_precat ((to_premor_monoidfun Add x y z f) : abgr_Abelian⟦_, _⟧)
                         (to_premor_monoidfun Add y x z (is_z_isomorphism_mor H)).
  Proof.
    use mk_is_inverse_in_precat.
    - use monoidfun_paths. use funextfun.
      intros x0. cbn. unfold to_premor. rewrite assoc.
      rewrite (is_inverse_in_precat2 H). use id_left.
    - use monoidfun_paths. use funextfun.
      intros x0. cbn. unfold to_premor. rewrite assoc.
      rewrite (is_inverse_in_precat1 H). use id_left.
  Qed.

  Lemma abgr_Additive_is_iso_premor {Add : Additive} (x y z : Add) {f : x --> y}
        (H : is_z_isomorphism f) :
    @is_z_isomorphism abgr_Abelian _ _ (to_premor_monoidfun Add x y z f).
  Proof.
    use mk_is_z_isomorphism.
    - exact (to_premor_monoidfun Add _ _ z (is_z_isomorphism_mor H)).
    - exact (abgr_Additive_is_iso_premor_inverses _ _ z H).
  Defined.

  (** *** f isomorphism ⇒ (_ · f) isomorphism *)

  Local Lemma abgr_Additive_is_iso_postmor_inverses {Add : Additive} (x y z : Add) {f : y --> z}
        (H : is_z_isomorphism f) :
    is_inverse_in_precat ((to_postmor_monoidfun Add x y z f) : abgr_Abelian⟦_, _⟧)
                         (to_postmor_monoidfun Add x z y (is_z_isomorphism_mor H)).
  Proof.
    use mk_is_inverse_in_precat.
    - use monoidfun_paths. use funextfun.
      intros x0. cbn. unfold to_postmor. rewrite <- assoc.
      rewrite (is_inverse_in_precat1 H). use id_right.
    - use monoidfun_paths. use funextfun.
      intros x0. cbn. unfold to_postmor. rewrite <- assoc.
      rewrite (is_inverse_in_precat2 H). use id_right.
  Qed.

  Lemma abgr_Additive_is_iso_postmor {Add : Additive} (x y z : Add) {f : y --> z}
        (H : is_z_isomorphism f) :
    @is_z_isomorphism abgr_Abelian _ _ (to_postmor_monoidfun Add x y z f).
  Proof.
    use mk_is_z_isomorphism.
    - exact (to_postmor_monoidfun Add x _ _ (is_z_isomorphism_mor H)).
    - exact (abgr_Additive_is_iso_postmor_inverses x _ _ H).
  Defined.

  (** *** Pre- and postcomposition with f is an isomorphism ⇒ f isomorphism *)

  Local Lemma abgr_Additive_premor_postmor_is_iso_inverses {Add : Additive} (x y : Add)
        {f : x --> y}
        (H1 : @is_z_isomorphism abgr_Abelian _ _ (to_premor_monoidfun Add x y x f))
        (H2 : @is_z_isomorphism abgr_Abelian _ _ (to_postmor_monoidfun Add y x y f)) :
    is_inverse_in_precat f ((is_z_isomorphism_mor H1 : monoidfun (to_abgrop x x) (to_abgrop y x))
                              (identity x : to_abgrop x x)).
  Proof.
    set (mor1 := ((is_z_isomorphism_mor H1) : (monoidfun (to_abgrop x x) (to_abgrop y x)))
                   ((identity x) : to_abgrop x x)).
    set (mor2 := ((is_z_isomorphism_mor H2) : (monoidfun (to_abgrop y y) (to_abgrop y x)))
                   ((identity y) : to_abgrop y y)).
    assert (Hx : f · mor1 = identity x).
    {
      exact (toforallpaths _ _ _ (base_paths _ _ (is_inverse_in_precat2 H1)) (identity x)).
    }
    assert (Hy : mor2 · f = identity y).
    {
      exact (toforallpaths _ _ _ (base_paths _ _ (is_inverse_in_precat2 H2)) (identity y)).
    }
    assert (H : mor1 = mor2).
    {
      rewrite <- (id_right mor2).
      rewrite <- Hx.
      rewrite assoc.
      rewrite Hy.
      rewrite id_left.
      use idpath.
    }
    use mk_is_inverse_in_precat.
    - exact Hx.
    - rewrite H. exact Hy.
  Qed.

  Lemma abgr_Additive_premor_postmor_is_iso {Add : Additive} (x y : Add) {f : x --> y}
        (H1 : @is_z_isomorphism abgr_Abelian _ _ (to_premor_monoidfun Add x y x f))
        (H2 : @is_z_isomorphism abgr_Abelian _ _ (to_postmor_monoidfun Add y x y f)) :
    is_z_isomorphism f.
  Proof.
    use mk_is_z_isomorphism.
    - exact (((is_z_isomorphism_mor H1) : (monoidfun (to_abgrop x x) (to_abgrop y x)))
               ((identity x) : to_abgrop x x)).
    - exact (abgr_Additive_premor_postmor_is_iso_inverses _ _ H1 H2).
  Defined.


  (** ** A criteria for isKernel which uses only the elements in the abelian group. *)

  Local Opaque ZeroArrow.

  Definition abgr_isKernel_iscontr {X Y Z W : abgr_Abelian} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = @ZeroArrow abgr_Abelian (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abgr_Abelian _ _ f) (h : W --> Y)
             (H' : h · g = @ZeroArrow abgr_Abelian (to_Zero abgr_Abelian) W Z) (w' : pr1 W) :
    iscontr (∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = pr1 h w').
  Proof.
    cbn in H'. rewrite <- (@PreAdditive_unel_zero (abgr_PreAdditive)) in H'.
    unfold to_unel in H'.
    set (e := toforallpaths _ _ _ (base_paths _ _ H') w').
    set (H'' := H (tpair _ (pr1 h w') e)).
    use (squash_to_prop H'' (isapropiscontr _)). intros HH.
    induction HH as [H1 H2]. cbn in H2.
    use tpair.
    - use tpair.
      + exact H1.
      + exact H2.
    - cbn. intros T. induction T as [T1 T2].
      use total2_paths_f.
      + use (abgr_monic_paths f isM T1 H1). cbn in H2. cbn.
        rewrite H2. rewrite T2. use idpath.
      + use proofirrelevance. use setproperty.
  Qed.

  Lemma abgr_isKernel_Criteria_ismonoidfun {X Y Z W : abgr_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D)∥)
             (isM : @isMonic abgr_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
             (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z) :
    ismonoidfun (λ w' : (W : abgr), pr1 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' w'))).
  Proof.
    use mk_ismonoidfun.
    - use mk_isbinopfun. intros x y. use (abgr_monic_paths f isM).
      use (pathscomp0 _ (! binopfunisbinopfun (f : monoidfun _ _) _ _)).
      use (pathscomp0 (pr2 (iscontrpr1 (abgr_isKernel_iscontr
                                          f g ZA H isM h H' ((x * y)%multmonoid))))).
      use (pathscomp0 (binopfunisbinopfun (h : monoidfun _ _) _ _)).
      use pathsinv0.
      use two_arg_paths.
      + exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (x%multmonoid)))).
      + exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (y%multmonoid)))).
    - use (abgr_monic_paths f isM).
      use (pathscomp0 (pr2 (iscontrpr1 (abgr_isKernel_iscontr
                                          f g ZA H isM h H' (unel (W : abgr)))))).
      use (pathscomp0 (monoidfununel h)). exact (! monoidfununel f).
  Qed.

  Lemma abgr_isKernel_Criteria_comm {X Y Z W : abgr_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abgr_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
             (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z) :
    monoidfuncomp (monoidfunconstr (abgr_isKernel_Criteria_ismonoidfun f g ZA H isM h H')) f = h.
  Proof.
    use monoidfun_paths. use funextfun. intros x.
    exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (x%multmonoid)))).
  Qed.

  Definition abgr_isKernel_Criteria_pair {X Y Z W : abgr_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abgr_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
             (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z) :
    ∑ ψ : abgr_Abelian ⟦W, X⟧, ψ · f = h.
  Proof.
    use tpair.
    - use monoidfunconstr.
      + intros w'. exact (pr1 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' w'))).
      + exact (abgr_isKernel_Criteria_ismonoidfun f g ZA H isM h H').
    - exact (abgr_isKernel_Criteria_comm f g ZA H isM h H').
  Defined.

  Lemma abgr_isKernel_Criteria_uniqueness {X Y Z W : abgr_category} (f : X --> Y) (g : Y --> Z)
        (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
        (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
             ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
        (isM : @isMonic abgr_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
        (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z)
        (t : ∑ ψ : abgr_Abelian ⟦W, X⟧, ψ · f = h) :
    t = abgr_isKernel_Criteria_pair f g ZA H isM h H'.
  Proof.
    use total2_paths_f.
    - use monoidfun_paths. use funextfun. intros x.
      use (abgr_monic_paths f isM).
      use (pathscomp0 (toforallpaths _ _ _ (base_paths _ _ (pr2 t)) x)). use pathsinv0.
      exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (x%multmonoid)))).
    - use proofirrelevance. use setproperty.
  Qed.

  Definition abgr_isKernel_Criteria {X Y Z : abgr_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abgr_category _ _ f) : isKernel (to_Zero abgr_Abelian) f g ZA.
  Proof.
    use mk_isKernel.
    - use homset_property.
    - intros w h H'. use iscontrpair.
      + exact (abgr_isKernel_Criteria_pair f g ZA H isM h H').
      + intros t. exact (abgr_isKernel_Criteria_uniqueness f g ZA H isM h H' t).
  Defined.

End abgr_corollaries.
