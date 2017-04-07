
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

  Variable (C : precategory) (hsC : has_homsets C) (Z : C).
  Local Notation "C / X" := (slice_precat C X hsC).
  Local Definition slice_eq {C : precategory} {hsC : has_homsets C} {x : C} {af bg : slice_precat C x hsC} (f g :slice_precat C x hsC ⟦ af, bg ⟧) : pr1 f = pr1 g → f = g :=
    eq_mor_slicecat hsC x af bg f g.

  (** ** function taking binary products in C / Z to pullbacks in C *)
  Definition binprod_to_pullback' {AZ BZ : C / Z} :
    BinProductCone (C / Z) AZ BZ → Pullback (pr2 AZ) (pr2 BZ).
  Proof.
    induction AZ as [A f].
    induction BZ as [B g].
    intros [[[P h] [[l leq] [r req]]] PisProd].
    refine ((P ,, l ,, r) ,, (! leq @ req) ,, _).
    intros Y j k Yeq. simpl in *.
    refine ((pr1 (pr1 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq)))) ,,
                 maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))) ,,
                 maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq)))))) ,, _).
    intros [t [tleq treq]].
    apply (invmaponpathsincl pr1).
    { apply isinclpr1.
      intros x.
      apply isofhleveldirprod;
        apply (hsC _ _).
    }
    assert (teq' : j · f = t · h).
    { rewrite <- tleq. rewrite leq.
      exact (!(assoc _ _ _)). }
    set (t' := (t ,, teq') : C / Z ⟦ Y ,, j · f , P,, h ⟧).
    assert (tmors : t' · ((l,, leq) : C / Z ⟦ (P ,, h), (A ,, f) ⟧) =
                    j,, idpath (j · f) × t' · ((r,, req) : C / Z ⟦ (P ,, h), (B ,, g)⟧) = k,, Yeq).
    {
      refine (slice_eq _ _ _ ,, slice_eq _ _ _);
        simpl; [exact tleq | exact treq].
    }
    exact (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq)) (t' ,, tmors)))).
  Defined.

   (** ** function taking pullbacks in C to binary products in C / Z *)
  Definition pullback_to_binprod' {A B : C} {f : A --> Z} {g : B --> Z} :
    Pullback f g -> BinProductCone (C / Z) (A ,, f) (B ,, g).
  Proof.
    intros [[P [l r]] [eq PisPull]].
    refine (((P ,, l · f) ,, ((l ,, idpath _) ,, (r ,, eq))) ,, _).
    intros [Y y] [j jeq] [k keq].
    set (yeq := jeq @ maponpaths (λ x , x · f) (!(pr1 (pr2 (pr1 (PisPull Y j k (!jeq @ keq))))))
                    @ !(assoc _ _ _)).
    set (leq := slice_eq (((pr1 (pr1 (PisPull Y j k (!jeq @ keq))) ,, yeq) : C / Z ⟦ (Y ,, y) , (P ,, _)⟧) · (l,, idpath (l · f) : C / Z ⟦ (P ,, _) , (A ,, f)⟧)) (j ,, jeq : C / Z ⟦ (Y ,, y) , (A ,, f)⟧) (pr1 (pr2 (pr1 (PisPull Y j k (!jeq @ keq)))))).
    set (req := slice_eq (((pr1 (pr1 (PisPull Y j k (!jeq @ keq))) ,, yeq) : C / Z ⟦ (Y ,, y) , (P ,, _)⟧) · (r,, eq : C / Z ⟦ (P ,, _) , (B ,, g)⟧)) (k ,, keq : C / Z ⟦ (Y ,, y) , (B ,, g)⟧) (pr2 (pr2 (pr1 (PisPull Y j k (!jeq @ keq)))))).
    refine (((pr1 (pr1 (PisPull Y j k (!jeq @ keq)))
                  ,, yeq) ,, (leq ,, req)) ,, _).
    intros [[t teq] [tleq treq]].
    apply (invmaponpathsincl pr1).
    { apply isinclpr1.
      intros x.
      apply isofhleveldirprod;
        apply (has_homsets_slice_precat _ _).
    }
    apply (@slice_eq C hsC).
    exact (maponpaths pr1 ((pr2 (PisPull Y j k (!jeq @ keq)))
                             (t ,, (maponpaths (slicecat_mor_morphism _ _) tleq
                                               ,, maponpaths (slicecat_mor_morphism _ _) treq)))).
  Defined.

  (** **  pullback_to_binprod' is invertible *)
  Lemma pullback_to_binprod_inv' {A B : C} {f : A --> Z} {g : B --> Z} (P : Pullback f g) :
    binprod_to_pullback' (pullback_to_binprod' P) = P.
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

  (** ** binprod_to_pullback' is invertible *)
  Lemma binprod_to_pullback_inv' {AZ BZ : C / Z} (P : BinProductCone (C / Z) AZ BZ) :
    pullback_to_binprod' (binprod_to_pullback' P) = P.
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
    - now apply (@slice_eq C hsC).
    - now rewrite transportf_const.
  Qed.

  (** ** function taking the type of all binary products in C / Z
         to the type of all pullbacks of functions to Z in C *)
  Definition binprod_to_pullback : (∑ AZ BZ , BinProductCone (C / Z) AZ BZ) →
                                   (∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g).
  Proof.
    intro P.
    induction P as [AZ BZ].
    induction BZ as [BZ P].
    exact (pr1 AZ ,, pr1 BZ ,, pr2 AZ ,, pr2 BZ ,, binprod_to_pullback' P).
  Defined.

  (** ** function taking the type of all pullbacks of functions to Z in C
         to the type of all binary products in C / Z  *)
  Definition pullback_to_binprod : (∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g) →
                                   (∑ AZ BZ , BinProductCone (C / Z) AZ BZ).
  Proof.
    intros [A [B [f [g P]]]].
    refine ((A ,, f) ,, (B ,, g) ,, pullback_to_binprod' P).
  Defined.

  (** ** binprod_to_pullback is invertible *)
  Lemma binprod_to_pullback_inv (P : ∑ AZ BZ , BinProductCone (C / Z) AZ BZ) :
    pullback_to_binprod (binprod_to_pullback P) = P.
  Proof.
    induction P as [[A f] [[B g] P]].
    unfold pullback_to_binprod , binprod_to_pullback.
    simpl.
    repeat (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf).
    now apply (binprod_to_pullback_inv' P).
  Qed.

  (** ** binprod_to_pullback is bijective *)
  Lemma bijective_binprod_to_pullback : bijective binprod_to_pullback.
  Proof.
    split.
    + intros [A [B [f [g P]]]].
      exists ((A ,, f) ,, (B ,, g) ,, pullback_to_binprod' P).
      unfold binprod_to_pullback. simpl (pr1 _). simpl (pr2 _).
      repeat (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf).
      now apply isaprop_isPullback.
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