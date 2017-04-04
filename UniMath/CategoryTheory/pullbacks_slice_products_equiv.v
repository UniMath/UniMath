
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

Local Open Scope cat.

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
  refine ((pr1 (pr1 (pr1 (PisProd (Y ,, compose j f) (j ,, idpath _) (k ,, Yeq)))) ,,
               maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, compose j f) (j ,, idpath _) (k ,, Yeq))))) ,,
               maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, compose j f) (j ,, idpath _) (k ,, Yeq)))))) ,, _).
  intros [t [tleq treq]].
  apply (invmaponpathsincl pr1).
  { apply isinclpr1.
    intros x.
    apply isofhleveldirprod;
      apply (hsC _ _).
  }
  assert (teq' : compose j f = compose t h).
  { rewrite <- tleq. rewrite leq.
    exact (!(assoc _ _ _)). }
  set (t' := (t ,, teq') : slice Z ⟦ Y ,, compose j f , P,, h ⟧).
  assert (tmors : compose t' ((l,, leq) : slice Z ⟦ (P ,, h), (A ,, f) ⟧) =
                  j,, idpath (compose j f) × compose t' ((r,, req) : slice Z ⟦ (P ,, h), (B ,, g)⟧) = k,, Yeq).
  {
    refine ((eq_mor_slicecat _ _ _ _ _ _ _) ,, (eq_mor_slicecat _ _ _ _ _ _ _));
    simpl; [exact tleq | exact treq].
  }
  exact (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, compose j f) (j ,, idpath _) (k ,, Yeq)) (t' ,, tmors)))).
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

Definition binprod_to_pullback : (∑ AZ BZ , BinProductCone (slice Z) AZ BZ) → (∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g).
Proof.
  intro P.
  induction P as [AZ BZ].
  induction BZ as [BZ P].
  exact (pr1 AZ ,, pr1 BZ ,, pr2 AZ ,, pr2 BZ ,, binprod_to_pullback_imp P).
Defined.

Local Lemma helper1 {T T' : UU} {P : T → UU} {Q : ∏ x : T , T' → P x  → UU} {a a' : T} {b b' : T'} {c : P a} {c' : P a'} {d : Q a b c} {d' : Q a' b' c'} :
  (a ,, b ,, c ,, d : ∑ x : T, (∑ y : T', (∑ p : P x, Q x y p))) = a' ,, b' ,, c' ,, d' → a ,, c = a' ,, c'.
Proof.
  intros eq.
  apply (total2_paths2_f (base_paths _ _ eq)).
  refine (_ @ base_paths _ _ (fiber_paths (fiber_paths eq))).
  rewrite transportf_total2. simpl.
  rewrite transportf_const. unfold idfun.
  rewrite transportf_total2. simpl.
  generalize (base_paths (a,, b,, c,, d) (a',, b',, c',, d') eq).
  clear eq. simpl. intro eq.
  induction eq.
  now rewrite idpath_transportf.
Defined.

Lemma bijective_binprod_to_pullback : bijective binprod_to_pullback.
Proof.
  split.
  + intros [A [B [f [g P]]]].
    exists ((A ,, f) ,, (B ,, g) ,, pullback_to_binprod_imp P).
    unfold binprod_to_pullback. simpl (pr1 _). simpl (pr2 _).
    repeat (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf).
    now apply pullback_to_binprod_imp_inv.
  + intros [[A f] [[B g] P]] [[A' f'] [[B' g'] P']] eq.
    induction P as [[[P h] [[l leq] [r req]]] PisProd].
    induction P' as [[[P' h'] [[l' leq'] [r' req']]] PisProd'].
    unfold binprod_to_pullback in eq. simpl in *.
    Check (helper1 eq).
    apply (total2_paths2_f (helper1 eq)).
    simpl.

Lemma isweq_binprod_to_pullback : isweq binprod_to_pullback.
Proof.
  intros [A [B [f [g P]]]].
  unfold iscontr. unfold hfiber. simpl.
  assert (invEq : binprod_to_pullback ((A ,, f) ,, (B ,, g) ,, pullback_to_binprod_imp P) = A,, B,, f,, g,, P).
  { unfold binprod_to_pullback. simpl (pr1 _). simpl (pr2 _).
    repeat (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf).
    now apply pullback_to_binprod_imp_inv.
  }
  exists (((A,, f),, (B,, g),, pullback_to_binprod_imp P) ,, invEq).
  intros [[[A' f'] [[B' g'] P']] eq'].
  assert (hl : isofhlevel 2 (∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g)).
  { admit. }
  apply (invmaponpathsincl pr1).
  + apply isofhlevelfpr1.
    intros ?.
    exact (hl (binprod_to_pullback x) (A,, B,, f,, g,, P)).
  + simpl.