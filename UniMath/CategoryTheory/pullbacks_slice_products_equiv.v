
(** **********************************************************

Matthew Weaver, 2017

 ************************************************************)


(** **********************************************************

Contents : Equivalence of binary products in C/Z to
           pullbacks of pairs of arrows to Z in C

 ************************************************************)


Require Import UniMath.MoreFoundations.Tactics
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.equivalences
        UniMath.CategoryTheory.limits.binproducts
        UniMath.CategoryTheory.limits.pullbacks.

Local Open Scope cat.

(** * Proof that the types of binary products in C/Z and pullbacks of pairs of arrows to Z in C are equivalent *)
Section pullbacks_slice_products_equiv.

  Context {C : precategory} (hsC : has_homsets C) (Z : C).
  Local Notation "C / X" := (slice_precat C X hsC).

  (** ** pullback_to_slice_binprod is invertible *)
  Lemma pullback_to_slice_binprod_inv {A B : C} {f : A --> Z} {g : B --> Z} (P : Pullback f g) :
    slice_binprod_to_pullback hsC (pullback_to_slice_binprod hsC P) = P.
  Proof.
    induction P as [[P [l r]] [Peq PisPull]].
    apply (invmaponpathsincl pr1).
    { apply isinclpr1.
      intros ?.
      apply isofhleveltotal2.
      + apply hsC.
      + intros ?.
        apply isaprop_isPullback.
    }
    reflexivity.
  Qed.

  (** ** slice_binprod_to_pullback is invertible *)
  Lemma slice_binprod_to_pullback_inv {AZ BZ : C / Z} (P : BinProductCone (C / Z) AZ BZ) :
    pullback_to_slice_binprod hsC (slice_binprod_to_pullback hsC P) = P.
  Proof.
    induction AZ as [A f].
    induction BZ as [B g].
    induction P as [[[P h] [[l leq] [r req]]] PisProd].
    apply (invmaponpathsincl pr1).
    { apply isinclpr1.
      intros ?.
      apply isaprop_isBinProductCone.
    }
    simpl in *.
    use total2_paths2_f.
    + apply (total2_paths2_f (idpath _)).
      rewrite idpath_transportf.
      exact (!leq).
    + induction (!leq). simpl.
      rewrite idpath_transportf.
      use total2_paths2_f.
    - now apply (eq_mor_slicecat hsC).
    - rewrite transportf_const.
      now apply (eq_mor_slicecat hsC).
  Qed.

  (** ** function taking the type of all binary products in C / Z
         to the type of all pullbacks of functions to Z in C *)
  Definition binprod_to_pullback : (∑ AZ BZ , BinProductCone (C / Z) AZ BZ) →
                                   (∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g).
  Proof.
    intro P.
    induction P as [AZ BZ].
    induction BZ as [BZ P].
    exact (pr1 AZ ,, pr1 BZ ,, pr2 AZ ,, pr2 BZ ,, slice_binprod_to_pullback hsC P).
  Defined.

  (** ** function taking the type of all pullbacks of functions to Z in C
         to the type of all binary products in C / Z  *)
  Definition pullback_to_binprod : (∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g) →
                                   (∑ AZ BZ , BinProductCone (C / Z) AZ BZ).
  Proof.
    intros [A [B [f [g P]]]].
    refine ((A ,, f) ,, (B ,, g) ,, pullback_to_slice_binprod hsC P).
  Defined.

  (** ** binprod_to_pullback is invertible *)
  Lemma binprod_to_pullback_inv (P : ∑ AZ BZ , BinProductCone (C / Z) AZ BZ) :
    pullback_to_binprod (binprod_to_pullback P) = P.
  Proof.
    induction P as [[A f] [[B g] P]].
    unfold pullback_to_binprod , binprod_to_pullback.
    simpl.
    repeat (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf).
    now apply (slice_binprod_to_pullback_inv P).
  Qed.

  (** ** binprod_to_pullback is bijective *)
  Lemma bijective_binprod_to_pullback : bijective binprod_to_pullback.
  Proof.
    split.
    + intros [A [B [f [g P]]]].
      exists ((A ,, f) ,, (B ,, g) ,, pullback_to_slice_binprod hsC P).
      unfold binprod_to_pullback. simpl (pr1 _). simpl (pr2 _).
      do 4 (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf);
      exact (pullback_to_slice_binprod_inv P).
    + intros x x' eq.
      set (eq' := maponpaths pullback_to_binprod eq).
      repeat rewrite binprod_to_pullback_inv in eq'.
      exact eq'.
  Qed.

  Definition isweq_binprod_to_pullback : isweq binprod_to_pullback :=
    bijection_to_weq _ bijective_binprod_to_pullback.

  (** ** the equivalence of the types of binary products in C/Z
         and pullbacks of pairs of arrows to Z in C *)
  Definition weq_binprod_to_pullback : weq _ _ := binprod_to_pullback ,, isweq_binprod_to_pullback.

End pullbacks_slice_products_equiv.