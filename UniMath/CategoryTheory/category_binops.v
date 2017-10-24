(* The category of sets with binary operations. *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.functor_categories.

Section BINOPS_precategory.

  Definition binops_fun_space (A B : setwithbinop) : hSet :=
    hSetpair _ (isasetbinopfun A B).

  Definition binops_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) setwithbinop
          (λ A B : setwithbinop, binops_fun_space A B).

  Definition idbinopfun (A : setwithbinop) : binopfun A A.
  Proof.
    use binopfunpair. intros a. exact a.
    intros a a'.
    apply idpath.
  Defined.

  Definition idbinopfun_remove_left (A B : setwithbinop) (f : binopfun A B) :
    binopfuncomp (idbinopfun A) f = f.
  Proof.
    unfold binopfuncomp. unfold idbinopfun.
    use total2_paths_f. cbn. unfold funcomp. apply maponpaths.
    apply idpath. apply proofirrelevance. apply isapropisbinopfun.
  Defined.


  Definition idbinopfun_remove_right (A B : setwithbinop) (f : binopfun A B) :
    binopfuncomp f (idbinopfun B) = f.
  Proof.
    unfold binopfuncomp. unfold idbinopfun.
    use total2_paths_f. cbn. unfold funcomp. apply maponpaths.
    apply idpath. apply proofirrelevance. apply isapropisbinopfun.
  Defined.

  Definition binopfuncomp_assoc (A B C D : setwithbinop) (f : binopfun A B)
             (g : binopfun B C) (h : binopfun C D) :
    binopfuncomp (binopfuncomp f g) h = binopfuncomp f (binopfuncomp g h).
  Proof.
    unfold binopfuncomp. apply maponpaths.
    apply isapropisbinopfun.
  Defined.

  Definition binop_precategory_data : precategory_data :=
    precategory_data_pair binops_precategory_ob_mor
                          (λ (A : setwithbinop), idbinopfun A )
                          (fun (A B C : setwithbinop) (f : binopfun A B)
                             (g : binopfun B C) => binopfuncomp f g).

  Lemma is_precategory_binop_precategory_data :
    is_precategory binop_precategory_data.
  Proof.
    repeat split; cbn.

    intros a b f. apply idbinopfun_remove_left.
    intros a b f. apply idbinopfun_remove_right.

    intros a b c d f g h. apply pathsinv0.
    apply (binopfuncomp_assoc a b c d f g h).
  Qed.

  Definition binop_precategory : precategory :=
    tpair _ _ is_precategory_binop_precategory_data.

  Local Notation BINOP := binop_precategory.
  Lemma has_homsets_BINOP : has_homsets BINOP.
  Proof. intros a b; apply isasetbinopfun. Qed.

End BINOPS_precategory.

Notation BINOP := binop_precategory.

Section BINOP_category.

  (** ** Equivalence between isomorphisms and binopisos *)

  Lemma binop_iso_is_equiv (A B : ob BINOP)
        (f : iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    apply (gradth _ (pr1binopfun _ _ (inv_from_iso f))).
    - intro x.
      set (T:=iso_inv_after_iso f).
      apply subtypeInjectivity in T.
      set (T':=toforallpaths _ _ _ T). apply T'.
      intro x0.
      apply isapropisbinopfun.
    - intros y.

      set (T:=iso_after_iso_inv f).
      apply subtypeInjectivity in T.
      set (T':=toforallpaths _ _ _ T). apply T'.
      intros x0.
      apply isapropisbinopfun.
  Defined.

  Lemma binop_iso_equiv (A B : ob BINOP) : iso A B -> binopiso A B.
  Proof.
    intro f.
    use binopisopair.
    set (X := binop_iso_is_equiv A B f).
    apply (weqpair (pr1 (pr1 f)) X).
    apply (pr2 (pr1 f)).
  Defined.

  Lemma binop_equiv_is_iso (A B : setwithbinop)
        (f : binopiso A B) :
    @is_iso BINOP A B (binopfunpair (pr1 (pr1 f)) (pr2 f)).
  Proof.
    apply (is_iso_qinv (C:=BINOP) _ (binopfunpair (pr1 (pr1 (invbinopiso f)))
                                                  (pr2 (invbinopiso f)))).
    split; cbn. unfold compose, identity. cbn. unfold binopfuncomp, idbinopfun.
    cbn. use total2_paths_f. cbn. apply funextfun. intros x.
    apply homotinvweqweq. cbn. apply impred_isaprop. intros t.
    apply impred_isaprop. intros t0. apply (pr2 (pr1 A)).

    use total2_paths_f. cbn. apply funextfun. intros x.
    apply homotweqinvweq. cbn. apply impred_isaprop. intros yt.
    apply impred_isaprop. intros t0. apply (pr2 (pr1 B)).
  Defined.

  Lemma binop_equiv_iso (A B : BINOP) : binopiso A B -> iso A B.
  Proof.
    intro f.
    cbn in *.
    set (T := binop_equiv_is_iso A B f).
    set (T' := @isopair BINOP _ _ (binopfunpair (pr1 (pr1 f)) (pr2 f)) T).
    apply T'.
  Defined.

  Lemma binop_iso_equiv_is_equiv (A B : BINOP) : isweq (binop_iso_equiv A B).
  Proof.
    apply (gradth _ (binop_equiv_iso A B)).
    intro; apply eq_iso. apply maponpaths.
    unfold binop_equiv_iso, binop_iso_equiv. cbn.
    use total2_paths_f. cbn. unfold binopfunpair.
    apply subtypeEquality. intros y. apply isapropisbinopfun.
    apply maponpaths. apply subtypeEquality.
    unfold isPredicate.

    intros x0. apply isapropisbinopfun.
    apply idpath.

    apply proofirrelevance.
    apply isaprop_is_iso.

    intros y. unfold binop_iso_equiv, binop_equiv_iso. cbn.
    use total2_paths_f. cbn. unfold binopfunpair.
    apply subtypeEquality. intros x. apply isapropisweq.
    apply idpath.

    apply proofirrelevance.
    apply isapropisbinopfun.
  Defined.

  Definition binop_iso_equiv_weq (A B : BINOP) : (iso A B) ≃ (binopiso A B).
  Proof.
    exists (binop_iso_equiv A B).
    apply binop_iso_equiv_is_equiv.
  Defined.

  Lemma binop_equiv_iso_is_equiv (A B : BINOP) : isweq (binop_equiv_iso A B).
  Proof.
    apply (gradth _ (binop_iso_equiv A B)).
    intros x. apply subtypeEquality.
    intros y. apply isapropisbinopfun.

    unfold binop_equiv_iso, binop_iso_equiv. cbn.
    use total2_paths_f. cbn. apply idpath.
    apply isapropisweq.

    intros y. unfold binop_equiv_iso, binop_iso_equiv. cbn.
    use total2_paths_f. cbn. unfold binopfunpair. cbn.
    apply subtypeEquality. intros x. apply isapropisbinopfun.
    apply idpath. apply proofirrelevance.
    apply isaprop_is_iso.
  Qed.

  Definition binop_equiv_iso_weq (A B : BINOP) :
    (binopiso A B) ≃ (iso A B).
  Proof.
    exists (binop_equiv_iso A B).
    apply binop_equiv_iso_is_equiv.
  Defined.

  Definition binop_precategory_isweq (a b : BINOP) :
    isweq (λ p : a = b, idtoiso p).
  Proof.
    use (@isweqhomot
           (a = b) (iso a b)
           (pr1weq (weqcomp (setwithbinop_univalence a b) (binop_equiv_iso_weq a b)))
           _ _ (weqproperty (weqcomp (setwithbinop_univalence a b) (binop_equiv_iso_weq a b)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque binop_precategory_isweq.

  Definition binop_precategory_is_univalent : is_univalent binop_precategory.
  Proof.
    use dirprodpair.
    - intros a b. exact (binop_precategory_isweq a b).
    - exact has_homsets_BINOP.
  Defined.

End BINOP_category.
