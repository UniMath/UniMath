
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

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g", left associativity).
Local Notation "# F" := (functor_on_morphisms F) (at level 3).

Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).

Variable (C : precategory) (hsC : has_homsets C) (Z : C).

Local Definition slice (X : C) := slice_precat C X hsC.

Definition binprod_to_pullback {AZ BZ : slice Z} :
  BinProductCone (slice Z) AZ BZ → Pullback (pr2 AZ) (pr2 BZ).
Proof.
  destruct AZ as [A f].
  destruct BZ as [B g].
  intros [[[P h] [[l leq] [r req]]] PisProd].
  refine ((P ,, l ,, r) ,, (! leq @ req) ,, _).
  intros Y j k Yeq. simpl in *.
  refine ((pr1 (pr1 (pr1 (PisProd (Y ,, j  ;; f) (j ,, idpath _) (k ,, Yeq)))) ,,
               maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, j  ;; f) (j ,, idpath _) (k ,, Yeq))))) ,,
               maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, j  ;; f) (j ,, idpath _) (k ,, Yeq)))))) ,, _).
  intros [t [tleq treq]].
  apply (invmaponpathsincl pr1).
  { apply isinclpr1.
    intros x.
    apply isofhleveldirprod;
      apply (hsC _ _).
  }
  assert (teq' : j ;; f = t ;; h).
  { rewrite <- tleq. rewrite leq.
    exact (!(assoc _ _ _)). }
  set (t' := (t ,, teq') : slice Z ⟦ Y ,, j ;; f , P,, h ⟧). 
  assert (tmors : t' ;; ((l,, leq) : slice Z ⟦ (P ,, h), (A ,, f) ⟧) =
                  j,, idpath (j ;; f) × t' ;; ((r,, req) : slice Z ⟦ (P ,, h), (B ,, g)⟧) = k,, Yeq).
  {
    refine ((eq_mor_slicecat _ _ _ _ _ _ _) ,, (eq_mor_slicecat _ _ _ _ _ _ _));
    simpl; [exact tleq | exact treq].
  }
  exact (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, j  ;; f) (j ,, idpath _) (k ,, Yeq)) (t' ,, tmors)))).
Defined.

Definition pullback_to_binprod {A B Z : C} {f : A --> Z} {g : B --> Z} :
  Pullback f g -> BinProductCone (slice Z) (A ,, f) (B ,, g).
Proof.
Admitted.

Lemma isweq_binprod_to_pullback {AZ BZ : slice Z} : isweq (@binprod_to_pullback AZ BZ).
Proof.
  destruct AZ as [A f].
  destruct BZ as [B g]. intros P'.
  refine ((pullback_to_binprod P' ,, _),, _).
  destruct P' as [[P [l r]] [Peq PisPullback]].
  simpl in l , r , Peq , PisPullback.
  intros [P' Peq'].
Admitted.