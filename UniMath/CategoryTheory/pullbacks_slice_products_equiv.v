
(** **********************************************************

Matthew Weaver, 2017

************************************************************)


(** **********************************************************

Contents : Equivalence of binary products in C/Z to
           pullbacks of pairs of arrows to Z in C

************************************************************)


Require Import UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.equivalences
        UniMath.CategoryTheory.limits.binproducts
        UniMath.CategoryTheory.limits.pullbacks.

(* Local Open Scope cat. SHOULD WORK! *)

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Local Notation "f ∙ g" := (compose f g) (at level 50, format "f  ∙  g", left associativity).
Local Notation "# F" := (functor_on_morphisms F) (at level 3).

Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).

Variable (C : precategory) (hsC : has_homsets C) (Z : C).

Local Definition slice (X : C) := slice_precat C X hsC.

Definition binprod_to_pullback_imp {AZ BZ : slice Z} :
  BinProductCone (slice Z) AZ BZ → Pullback (pr2 AZ) (pr2 BZ).
Proof.
  destruct AZ as [A f].
  destruct BZ as [B g].
  intros [[[P h] [[l leq] [r req]]] PisProd].
  refine ((P ,, l ,, r) ,, (! leq @ req) ,, _).
  intros Y j k Yeq. simpl in *.
  refine ((pr1 (pr1 (pr1 (PisProd (Y ,, j  ∙ f) (j ,, idpath _) (k ,, Yeq)))) ,,
               maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, j  ∙ f) (j ,, idpath _) (k ,, Yeq))))) ,,
               maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, j  ∙ f) (j ,, idpath _) (k ,, Yeq)))))) ,, _).
  intros [t [tleq treq]].
  apply (invmaponpathsincl pr1).
  { apply isinclpr1.
    intros x.
    apply isofhleveldirprod;
      apply (hsC _ _).
  }
  assert (teq' : j ∙ f = t ∙ h).
  { rewrite <- tleq. rewrite leq.
    exact (!(assoc _ _ _)). }
  set (t' := (t ,, teq') : slice Z ⟦ Y ,, j ∙ f , P,, h ⟧). 
  assert (tmors : t' ∙ ((l,, leq) : slice Z ⟦ (P ,, h), (A ,, f) ⟧) =
                  j,, idpath (j ∙ f) × t' ∙ ((r,, req) : slice Z ⟦ (P ,, h), (B ,, g)⟧) = k,, Yeq).
  {
    refine ((eq_mor_slicecat _ _ _ _ _ _ _) ,, (eq_mor_slicecat _ _ _ _ _ _ _));
    simpl; [exact tleq | exact treq].
  }
  exact (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, j  ∙ f) (j ,, idpath _) (k ,, Yeq)) (t' ,, tmors)))).
Defined.

Definition pullback_to_binprod_imp {A B : C} {f : A --> Z} {g : B --> Z} :
  Pullback f g -> BinProductCone (slice Z) (A ,, f) (B ,, g).
Proof.
Admitted.

Lemma pullback_to_binprod_imp_inv {A B : C} {f : A --> Z} {g : B --> Z} (P : Pullback f g) :
  binprod_to_pullback_imp (pullback_to_binprod_imp P) = P.
Admitted.

Lemma isweq_binprod_to_pullback_imp {AZ BZ : slice Z} : isweq (@binprod_to_pullback_imp AZ BZ).
Proof.
  destruct AZ as [A f].
  destruct BZ as [B g]. intros P'.
  refine ((pullback_to_binprod_imp P' ,, _),, _).
  destruct P' as [[P [l r]] [Peq PisPullback]].
  simpl in l , r , Peq , PisPullback.
  intros [P' Peq'].
Admitted.

Definition binprod_to_pullback : (∑ AZ BZ , BinProductCone (slice Z) AZ BZ) → (∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g) :=
  fun p => match p with
           | (AZ ,, BZ ,, P) => (pr1 AZ ,, pr1 BZ ,, pr2 AZ ,, pr2 BZ ,, binprod_to_pullback_imp P)
           end.

Lemma isweq_binprod_to_pullback : isweq binprod_to_pullback.
Proof.
  intros [A [B [f [g P]]]].
  unfold iscontr. unfold hfiber. simpl.
  assert (invEq : binprod_to_pullback ((A ,, f) ,, (B ,, g) ,, pullback_to_binprod_imp P) = A,, B,, f,, g,, P).
  {unfold binprod_to_pullback. simpl (pr1 _). simpl (pr2 _).
   refine (total2_paths2 (idpath A) (total2_paths2 (idpath B) (total2_paths2 (idpath f) (total2_paths2 (idpath g) _)))).
   exact (total2_paths2 (idpath A) (total2_paths2 (idpath B) (total2_paths2 (idpath f) (total2_paths2 (idpath g) (pullback_to_binprod_imp_inv P))))).
    admit. }

    Check (total2_paths2 (idpath A) (total2_paths2 (idpath B) (total2_paths2 (idpath f) (total2_paths2 (idpath g) (pullback_to_binprod_imp_inv P))))).

  refine ((((A ,, f) ,, (B ,, g) ,, pullback_to_binprod_imp P) ,, invEq) ,, _).
  intros [[AZ [BZ Pr]] Preq].
  apply (invmaponpathsincl pr1).
  { apply isinclpr1.
    intros [AZ' [BZ' Pr']]. simpl. Check isofhleveltotal2.
  }