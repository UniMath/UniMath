(**

This file contains proofs that the following functors are
(omega-)cocontinuous:

- Constant functor: F_x : C -> D, c |-> x
  [is_omega_cocont_constant_functor]
- Identity functor
  [is_omega_cocont_functor_identity]
- Composition of omega-cocontinuous functors
  [is_omega_cocont_functor_composite]
- Iteration of omega-cocontinuous functors: F^n : C -> C
  [is_omega_cocont_iter_functor]
- Pairing of omega-cocont functors (F,G) : A * B -> C * D, (x,y) |-> (F x,G y)
  [is_omega_cocont_binproduct_pair_functor]
- Indexed families of omega-cocont functors F^I : A^I -> B^I
  [is_omega_cocont_pair_functor]
- Binary delta functor: C -> C^2, x |-> (x,x)
  [cocont_bindelta_functor] [is_omega_cocont_bindelta_functor]
- General delta functor: C -> C^I
  [is_omega_cocont_delta_functor]
- Binary coproduct functor: C^2 -> C, (x,y) |-> x + y
  [cocont_bincoproduct_functor] [is_omega_cocont_bincoproduct_functor]
- General coproduct functor: C^I -> C
  [cocont_indexed_coproduct_functor] [is_omega_cocont_indexed_coproduct_functor]
- Binary coproduct of functors: F + G : C -> D, x |-> (x,x) |-> (F x,G x) |-> F x + G x
  [is_omega_cocont_BinCoproduct_of_functors_alt] [is_omega_cocont_BinCoproduct_of_functors]
- Coproduct of families of functors: + F_i : C -> D  (generalization of coproduct of functors)
  [is_omega_cocont_coproduct_of_functors_alt] [is_omega_cocont_coproduct_of_functors]
- Binary coproduct functor: F + G : C -> D, x |-> F x + G x
- General coproduct functor: + F_i : C -> D
- Constant product functors: C -> C, x |-> a * x  and  x |-> x * a
- Binary product functor: C^2 -> C, (x,y) |-> x * y
  [is_omega_cocont_binproduct_functor]
- Product of functors: F * G : C -> D, x |-> (x,x) |-> (F x,G x) |-> F x * G x
- Product functor: F * G : C -> D, x |-> F x * G x
- Precomposition functor: _ o K : [C,A] -> [M,A] for K : M -> C


Written by: Anders Mörtberg, 2015-2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.cats.limits.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.CommaCategories.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section move_upstream.

Lemma paireta {A B : UU} (p : A × B) : p = (pr1 p,, pr2 p).
Proof.
destruct p; apply idpath.
Defined.

End move_upstream.

Section cocont_functors.

(** The constant functor is omega cocontinuous *)
Lemma is_omega_cocont_constant_functor (C D : precategory) (hsD : has_homsets D)
  (x : D) : is_omega_cocont (constant_functor C D x).
Proof.
intros c L ccL HcL y ccy; simpl.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + apply (coconeIn ccy 0).
  + abstract (simpl; intro n; rewrite id_left;
              destruct ccy as [f Hf]; simpl in *;
              induction n; [apply idpath|];
              now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left).
- abstract (simpl; intro p; apply subtypeEquality;
              [ intros f; apply impred; intro; apply hsD
              | now simpl; destruct p as [p H]; rewrite <- (H 0), id_left]).
Defined.

Definition omega_cocont_constant_functor (C D : precategory) (hsD : has_homsets D)
  (x : D) : omega_cocont_functor C D := tpair _ _ (is_omega_cocont_constant_functor C D hsD x).

(** The identity functor is omega cocontinuous *)
Lemma is_omega_cocont_functor_identity (C : precategory) (hsC : has_homsets C) :
  is_omega_cocont (functor_identity C).
Proof.
intros c L ccL HcL.
apply (preserves_colimit_identity hsC _ _ _ HcL).
Defined.

Definition omega_cocont_functor_identity (C : precategory) (hsC : has_homsets C) :
  omega_cocont_functor C C := tpair _ _ (is_omega_cocont_functor_identity C hsC).

(** Functor composition preserves omega cocontinuity *)
Lemma is_omega_cocont_functor_composite {C D E : precategory}
  (hsE : has_homsets E) (F : functor C D) (G : functor D E) :
  is_omega_cocont F -> is_omega_cocont G -> is_omega_cocont (functor_composite F G).
Proof.
intros hF hG c L cc.
apply (preserves_colimit_comp hsE); [ apply hF | apply hG ].
Defined.

Definition omega_cocont_functor_composite {C D E : precategory}
  (hsE : has_homsets E) (F : omega_cocont_functor C D) (G : omega_cocont_functor D E) :
  omega_cocont_functor C E := tpair _ _ (is_omega_cocont_functor_composite hsE _ _ (pr2 F) (pr2 G)).

(** Functor iteration preserves omega cocontinuity *)
Lemma is_omega_cocont_iter_functor {C : precategory} (hsC : has_homsets C)
  (F : functor C C) (hF : is_omega_cocont F) n : is_omega_cocont (iter_functor F n).
Proof.
induction n as [|n IH]; simpl.
- apply (is_omega_cocont_functor_identity _ hsC).
- apply (is_omega_cocont_functor_composite hsC _ _ IH hF).
Defined.

Definition omega_cocont_iter_functor {C : precategory} (hsC : has_homsets C)
  (F : omega_cocont_functor C C) n : omega_cocont_functor C C :=
  tpair _ _ (is_omega_cocont_iter_functor hsC _ (pr2 F) n).

(** A pair of functors (F,G) : A * B -> C * D is omega_cocont if F and G are *)
Section binproduct_pair_functor.

Variables A B C D : precategory.
Variables (F : functor A C) (G : functor B D).
Variables (hsA : has_homsets A) (hsB : has_homsets B).
Variables (hsC : has_homsets C) (hsD : has_homsets D).

(* Maybe generalize these to arbitrary diagrams? *)
Lemma cocone_pr1_functor (cAB : chain (binproduct_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) :
  cocone (mapchain (pr1_functor A B)cAB) (ob1 ab).
Proof.
simple refine (mk_cocone _ _).
- simpl; intro n; apply (mor1 (coconeIn ccab n)).
- abstract (simpl; intros m n e; now rewrite <- (coconeInCommutes ccab m n e)).
Defined.

Lemma isColimCocone_pr1_functor (cAB : chain (binproduct_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) (Hccab : isColimCocone cAB ab ccab) :
   isColimCocone (mapchain (pr1_functor A B) cAB) (ob1 ab)
     (mapcocone (pr1_functor A B) cAB ccab).
Proof.
intros x ccx.
simple refine (let HHH : cocone cAB (x,, ob2 ab) := _ in _).
{ simple refine (mk_cocone _ _).
  - simpl; intro n; split;
      [ apply (pr1 ccx n) | apply (# (pr2_functor A B) (pr1 ccab n)) ].
  - abstract(
    simpl; intros m n e; rewrite (paireta (dmor cAB e));
    apply pathsdirprod; [ apply (pr2 ccx m n e)
                        | apply (maponpaths dirprod_pr2 ((pr2 ccab) m n e)) ]).
}
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2]; simpl in *.
mkpair.
- apply (tpair _ x1).
  abstract (intro n; apply (maponpaths pr1 (p1 n))).
- intro t.
  simple refine (let X : Σ x0,
           Π v : nat, coconeIn ccab v ;; x0 =
                      binprodcatmor (pr1 ccx v) (pr2 (pr1 ccab v)) := _ in _).
  { mkpair.
    - split; [ apply (pr1 t) | apply (identity _) ].
    - abstract (intro n; rewrite id_right; apply pathsdirprod;
                 [ apply (pr2 t) | apply idpath ]).
  }
  abstract (apply subtypeEquality; simpl;
            [ intro f; apply impred; intro; apply hsA
            | apply (maponpaths (fun x => pr1 (pr1 x)) (p2 X))]).
Defined.

Lemma is_omega_cocont_pr1_functor : is_omega_cocont (pr1_functor A B).
Proof.
intros c L ccL M.
now apply isColimCocone_pr1_functor.
Defined.

Lemma cocone_pr2_functor (cAB : chain (binproduct_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) :
  cocone (mapchain (pr2_functor A B) cAB) (pr2 ab).
Proof.
simple refine (mk_cocone _ _).
- simpl; intro n; apply (pr2 (coconeIn ccab n)).
- abstract (simpl; intros m n e; now rewrite <- (coconeInCommutes ccab m n e)).
Defined.

Lemma isColimCocone_pr2_functor (cAB : chain (binproduct_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) (Hccab : isColimCocone cAB ab ccab) :
   isColimCocone (mapchain (pr2_functor A B) cAB) (pr2 ab)
     (mapcocone (pr2_functor A B) cAB ccab).
Proof.
intros x ccx.
simple refine (let HHH : cocone cAB (pr1 ab,, x) := _ in _).
{ simple refine (mk_cocone _ _).
  - simpl; intro n; split;
      [ apply (# (pr1_functor A B) (pr1 ccab n)) | apply (pr1 ccx n) ].
  - abstract(
    simpl; intros m n e; rewrite (paireta (dmor cAB e)); apply pathsdirprod;
      [ apply (maponpaths pr1 (pr2 ccab m n e)) | apply (pr2 ccx m n e) ]).
 }
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2]; simpl in *.
mkpair.
- apply (tpair _ x2).
  abstract (intro n; apply (maponpaths dirprod_pr2 (p1 n))).
- intro t.
  simple refine (let X : Σ x0,
           Π v : nat, coconeIn ccab v ;; x0 =
                      binprodcatmor (pr1 (pr1 ccab v)) (pr1 ccx v) := _ in _).
  { mkpair.
    - split; [ apply (identity _) | apply (pr1 t) ].
    - abstract (intro n; rewrite id_right; apply pathsdirprod;
                 [ apply idpath | apply (pr2 t) ]).
  }
  abstract (apply subtypeEquality; simpl;
              [ intro f; apply impred; intro; apply hsB
              | apply (maponpaths (fun x => dirprod_pr2 (pr1 x)) (p2 X)) ]).
Defined.

Lemma is_omega_cocont_pr2_functor : is_omega_cocont (pr2_functor A B).
Proof.
intros c L ccL M.
now apply isColimCocone_pr2_functor.
Defined.

Lemma is_omega_cocont_binproduct_pair_functor (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (binproduct_pair_functor F G).
Proof.
intros cAB ml ccml Hccml xy ccxy; simpl in *.
simple refine (let cFAX : cocone (mapdiagram F (mapchain (pr1_functor A B) cAB))
                                 (pr1 xy) := _ in _).
{ simple refine (mk_cocone _ _).
  - intro n; apply (pr1 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths pr1 (pr2 ccxy m n e))).
}
simple refine (let cGBY : cocone (mapdiagram G (mapchain (pr2_functor A B)cAB))
                                 (pr2 xy) := _ in _).
{ simple refine (mk_cocone _ _).
  - intro n; apply (pr2 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr2 (pr2 ccxy m n e))).
}
destruct (HF _ _ _ (isColimCocone_pr1_functor cAB ml ccml Hccml) _ cFAX) as [[f hf1] hf2].
destruct (HG _ _ _ (isColimCocone_pr2_functor cAB ml ccml Hccml) _ cGBY) as [[g hg1] hg2].
simpl in *.
mkpair.
- apply (tpair _ (f,,g)).
  abstract (intro n; unfold binprodcatmor, compose; simpl;
            now rewrite hf1, hg1, (paireta (coconeIn ccxy n))).
- intro t.
  apply subtypeEquality; simpl.
  + intro x; apply impred; intro.
    apply isaset_dirprod; [ apply hsC | apply hsD ].
  + destruct t as [[f1 f2] ?]; simpl in *.
    apply pathsdirprod.
    * apply (maponpaths pr1 (hf2 (f1,, (λ n, maponpaths pr1 (p n))))).
    * apply (maponpaths pr1 (hg2 (f2,, (λ n, maponpaths dirprod_pr2 (p n))))).
Defined.

End binproduct_pair_functor.

(** A family of functor F^I : A^I -> B^I is omega_cocont if each F_i is *)
Section pair_functor.

Variables (I : UU) (A B : precategory).
Variables (F : Π (i : I), functor A B).
Variables (hsA : has_homsets A) (hsB : has_homsets B).

(* I needs to have decidable equality for pr_functor to be omega cocont *)
Hypothesis (HI : isdeceq I).

Definition ifI (i j : I) (a b : A) : A := match HI i j with
  | ii1 _ => a
  | ii2 _ => b
  end.

Lemma ifI_eq i x y : ifI i i x y = x.
Proof.
now unfold ifI; destruct (HI i i) as [p|p]; [|destruct (p (idpath _))].
Defined.

Lemma isColimCocone_pr_functor
  (c : chain (power_precategory I A))
  (L : power_precategory I A) (ccL : cocone c L)
  (M : isColimCocone c L ccL) : Π i,
  isColimCocone _ _ (mapcocone (pr_functor I (fun _ => A) i) c ccL).
Proof.
intros i x ccx; simpl in *.
simple refine (let HHH : cocone c (fun j => ifI i j x (L j)) := _ in _).
{ unfold ifI.
  simple refine (mk_cocone _ _).
  - simpl; intros n j.
    destruct (HI i j) as [p|p].
    + apply (transportf (fun i => A ⟦ dob c n i, x ⟧) p (coconeIn ccx n)).
    + apply (# (pr_functor I (fun _ => A) j) (coconeIn ccL n)).
  - abstract (simpl; intros m n e;
      apply funextsec; intro j; unfold compose; simpl;
      destruct (HI i j);
        [ destruct p; apply (pr2 ccx m n e)
        | apply (toforallpaths _ _ _ (pr2 ccL m n e) j)]).
}
destruct (M _ HHH) as [[x1 p1] p2].
mkpair.
- apply (tpair _ (transportf _ (ifI_eq _ _ _) (x1 i))).
  abstract (intro n;
    rewrite <- idtoiso_postcompose, assoc;
    eapply pathscomp0;
      [eapply cancel_postcomposition, (toforallpaths _ _ _ (p1 n) i)|];
    unfold ifI, ifI_eq; simpl;
    destruct (HI i i); [|destruct (n0 (idpath _))];
    rewrite idtoiso_postcompose, idpath_transportf;
    assert (hp : p = idpath i); [apply (isasetifdeceq _ HI)|];
    now rewrite hp, idpath_transportf).
- intro t.
  simple refine (let X : Σ x0,
           Π n, coconeIn ccL n ;; x0 = coconeIn HHH n := _ in _).
  { mkpair.
    - simpl; intro j; unfold ifI.
      destruct (HI i j).
      + apply (transportf (fun i => A ⟦ L i, x ⟧) p (pr1 t)).
      + apply identity.
    - abstract (intro n; apply funextsec; intro j; unfold ifI; destruct (HI i j);
          [ now destruct p; rewrite <- (pr2 t), !idpath_transportf
          | apply id_right ]).
  }
  apply subtypeEquality; simpl; [intro f; apply impred; intro; apply hsA|].
  set (H := toforallpaths _ _ _ (maponpaths pr1 (p2 X)) i); simpl in H.
  rewrite <- H; clear H; unfold ifI_eq, ifI.
  destruct (HI i i) as [p|p]; [|destruct (p (idpath _))].
  assert (hp : p = idpath i); [apply (isasetifdeceq _ HI)|].
  now rewrite hp, idpath_transportf.
Defined.

Lemma is_omega_cocont_pr_functor (i : I) : is_omega_cocont (pr_functor I (fun _ => A) i).
Proof.
intros c L ccL M.
now apply isColimCocone_pr_functor.
Defined.

Lemma is_omega_cocont_pair_functor
  (HF : Π (i : I), is_omega_cocont (F i)) :
  is_omega_cocont (pair_functor I F).
Proof.
intros cAB ml ccml Hccml xy ccxy; simpl in *.
simple refine (let cc i : cocone (mapdiagram (F i)
                            (mapdiagram (pr_functor I (fun _ => A) i) cAB)) (xy i) := _ in _).
{ simple refine (mk_cocone _ _).
  - intro n; apply (pr1 ccxy n).
  - abstract (intros m n e;
              apply (toforallpaths _ _ _ (pr2 ccxy m n e) i)).
}
set (X i := HF i _ _ _ (isColimCocone_pr_functor _ _ _ Hccml i) (xy i) (cc i)).
mkpair.
- mkpair.
  + intro i; apply (pr1 (pr1 (X i))).
  + abstract (intro n; apply funextsec; intro j; apply (pr2 (pr1 (X j)) n)).
- intro t.
  apply subtypeEquality; simpl.
  + intro x; apply impred; intro; apply impred_isaset; intro i; apply hsB.
  + destruct t as [f1 f2]; simpl in *.
    apply funextsec; intro i.
    simple refine (let H : Σ x : B ⟦ (F i) (ml i), xy i ⟧,
                          Π n, # (F i) (coconeIn ccml n i) ;; x =
                               coconeIn ccxy n i := _ in _).
    { apply (tpair _ (f1 i)); intro n; apply (toforallpaths _ _ _ (f2 n) i). }
    apply (maponpaths pr1 (pr2 (X i) H)).
Defined.

End pair_functor.

(** The bindelta functor C -> C^2 mapping x to (x,x) is omega_cocont *)
Section bindelta_functor.

Variables (C : precategory) (PC : BinProducts C) (hsC : has_homsets C).

Lemma cocont_bindelta_functor : is_cocont (bindelta_functor C).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_bindelta_functor PC) hsC).
abstract (apply (has_homsets_binproduct_precategory _ _ hsC hsC)).
Defined.

Lemma is_omega_cocont_bindelta_functor : is_omega_cocont (bindelta_functor C).
Proof.
intros c L ccL.
apply cocont_bindelta_functor.
Defined.

End bindelta_functor.

(** The generalized delta functor C -> C^I is omega_cocont *)
Section delta_functor.

Variables (I : UU) (C : precategory) (PC : Products I C) (hsC : has_homsets C).

Lemma cocont_delta_functor : is_cocont (delta_functor I C).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_delta_functor _ PC) hsC).
abstract (apply (has_homsets_power_precategory _ _ hsC)).
Defined.

Lemma is_omega_cocont_delta_functor :
  is_omega_cocont (delta_functor I C).
Proof.
intros c L ccL.
apply cocont_delta_functor.
Defined.

End delta_functor.

(** The functor "+ : C^2 -> C" is cocont *)
Section bincoprod_functor.

Variables (C : precategory) (PC : BinCoproducts C) (hsC : has_homsets C).

Lemma cocont_bincoproduct_functor : is_cocont (bincoproduct_functor PC).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_bincoproduct_functor PC)).
- abstract (apply has_homsets_binproduct_precategory; apply hsC).
- abstract (apply hsC).
Defined.

Lemma is_omega_cocont_bincoproduct_functor :
  is_omega_cocont (bincoproduct_functor PC).
Proof.
intros c L ccL; apply cocont_bincoproduct_functor.
Defined.

End bincoprod_functor.

(** The functor "+ : C^I -> C" is cocont *)
Section coprod_functor.

Variables (I : UU) (C : precategory) (PC : Coproducts I C).
Variable (hsC : has_homsets C).

Lemma cocont_indexed_coproduct_functor :
  is_cocont (indexed_coproduct_functor _ PC).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_indexed_coproduct_functor _ PC)).
- abstract (apply has_homsets_power_precategory; apply hsC).
- abstract (apply hsC).
Defined.

Lemma is_omega_cocont_indexed_coproduct_functor :
  is_omega_cocont (indexed_coproduct_functor _ PC).
Proof.
intros c L ccL; apply cocont_indexed_coproduct_functor.
Defined.

End coprod_functor.

Section BinCoproduct_of_functors.

Variables (C D : precategory) (PC : BinProducts C) (HD : BinCoproducts D).
Variables (hsC : has_homsets C) (hsD : has_homsets D).

Lemma is_omega_cocont_BinCoproduct_of_functors_alt (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinCoproduct_of_functors_alt HD F G).
Proof.
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_bindelta_functor _ PC hsC).
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_binproduct_pair_functor _ _ _ _ _ _ hsC hsC hsD hsD HF HG).
apply (is_omega_cocont_bincoproduct_functor _ _ hsD).
Defined.

Definition omega_cocont_BinCoproduct_of_functors_alt (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinCoproduct_of_functors_alt _ _ (pr2 F) (pr2 G)).

Lemma is_omega_cocont_BinCoproduct_of_functors (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinCoproduct_of_functors _ _ HD F G).
Proof.
exact (transportf _
         (BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors C D HD hsD F G)
         (is_omega_cocont_BinCoproduct_of_functors_alt _ _ HF HG)).
Defined.

Definition omega_cocont_BinCoproduct_of_functors
 (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinCoproduct_of_functors _ _ (pr2 F) (pr2 G)).

End BinCoproduct_of_functors.

Section coproduct_of_functors.

Variables (I : UU) (C D : precategory) (PC : Products I C).
Variables (HD : Coproducts I D).
Variables (hsC : has_homsets C) (hsD : has_homsets D).
Variable (HI : isdeceq I).

Lemma is_omega_cocont_coproduct_of_functors_alt (F : Π i, functor C D)
  (HF : Π i, is_omega_cocont (F i)) :
  is_omega_cocont (coproduct_of_functors_alt _ HD F).
Proof.
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_delta_functor _ _ PC hsC).
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_pair_functor _ _ _ _ hsC hsD HI HF).
apply (is_omega_cocont_indexed_coproduct_functor _ _ _ hsD).
Defined.

Definition omega_cocont_coproduct_of_functors_alt
  (F : Π i, omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_coproduct_of_functors_alt _ (fun i => pr2 (F i))).

Lemma is_omega_cocont_coproduct_of_functors (F : Π (i : I), functor C D)
  (HF : Π i, is_omega_cocont (F i)) :
  is_omega_cocont (coproduct_of_functors I _ _ HD F).
Proof.
exact (transportf _
        (coproduct_of_functors_alt_eq_coproduct_of_functors I C D HD hsD F)
        (is_omega_cocont_coproduct_of_functors_alt _ HF)).
Defined.

Definition omega_cocont_coproduct_of_functors
  (F : Π i, omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_coproduct_of_functors _ (fun i => pr2 (F i))).

End coproduct_of_functors.

Section constprod_functors.

Variables (C : precategory) (PC : BinProducts C) (hsC : has_homsets C).
Variables (hE : has_exponentials PC).

Lemma cocont_constprod_functor1 (x : C) : is_cocont (constprod_functor1 PC x).
Proof.
apply (left_adjoint_cocont _ (hE _) hsC hsC).
Defined.

Lemma is_omega_cocont_constprod_functor1 (x : C) : is_omega_cocont (constprod_functor1 PC x).
Proof.
intros c L ccL.
apply cocont_constprod_functor1.
Defined.

Definition omega_cocont_constprod_functor1 (x : C) :
  omega_cocont_functor C C := tpair _ _ (is_omega_cocont_constprod_functor1 x).

Lemma cocont_constprod_functor2 (x : C) : is_cocont (constprod_functor2 PC x).
Proof.
apply left_adjoint_cocont; try apply hsC.
apply (is_left_adjoint_constprod_functor2 PC hsC), hE.
Defined.

Lemma is_omega_cocont_constprod_functor2 (x : C) : is_omega_cocont (constprod_functor2 PC x).
Proof.
intros c L ccL.
apply cocont_constprod_functor2.
Defined.

Definition omega_cocont_constprod_functor2 (x : C) :
  omega_cocont_functor C C := tpair _ _ (is_omega_cocont_constprod_functor2 x).

End constprod_functors.

(** The functor "* : C^2 -> C" is omega cocont *)
Section binprod_functor.

Variables (C : precategory) (PC : BinProducts C) (hsC : has_homsets C).
Variables (hE : has_exponentials PC).

Definition fun_lt (cAB : chain (binproduct_precategory C C)) :
  Π i j, i < j ->
              C ⟦ BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))),
                  BinProductObject C (PC (ob1 (dob cAB j)) (ob2 (dob cAB j))) ⟧.
Proof.
intros i j hij.
apply (BinProductOfArrows _ _ _ (mor1 (chain_mor cAB _ _ hij)) (identity _)).
Defined.

Definition fun_gt (cAB : chain (binproduct_precategory C C)) :
  Π i j, i > j ->
              C ⟦ BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))),
                  BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB i))) ⟧.
Proof.
intros i j hij.
apply (BinProductOfArrows _ _ _ (identity _) (mor2 (chain_mor cAB _ _ hij))).
Defined.

(* The map to K from the "grid" *)
Definition map_to_K (cAB : chain (binproduct_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) i j :
  C⟦BinProductObject C (PC (ob1 (dob cAB i)) (ob2 (dob cAB j))), K⟧.
Proof.
destruct (natlthorgeh i j).
- apply (fun_lt cAB _ _ h ;; coconeIn ccK j).
- destruct (natgehchoice _ _ h) as [H|H].
  * apply (fun_gt cAB _ _ H ;; coconeIn ccK i).
  * destruct H; apply (coconeIn ccK i).
Defined.

Lemma map_to_K_commutes (cAB : chain (binproduct_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K)
  i j k (e : edge j k) :
   BinProduct_of_functors_mor C C PC (constant_functor C C (pr1 (pr1 cAB i)))
     (functor_identity C) (pr2 (dob cAB j)) (pr2 (dob cAB k))
     (mor2 (dmor cAB e)) ;; map_to_K cAB K ccK i k =
   map_to_K cAB K ccK i j.
Proof.
destruct e; simpl.
unfold BinProduct_of_functors_mor, map_to_K.
destruct (natlthorgeh i j) as [h|h].
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * rewrite assoc, <- (coconeInCommutes ccK j (S j) (idpath _)), assoc; simpl.
    apply cancel_postcomposition; unfold fun_lt.
    rewrite BinProductOfArrows_comp, id_left.
    eapply pathscomp0; [apply BinProductOfArrows_comp|].
    rewrite id_right.
    apply BinProductOfArrows_eq; trivial.
    rewrite id_left; simpl.
    destruct (natlehchoice4 i j h0) as [h1|h1].
    + apply cancel_postcomposition, maponpaths, maponpaths, isasetbool.
    + destruct h1; destruct (isirreflnatlth _ h).
  * destruct (isirreflnatlth _ (natlthlehtrans _ _ _ (natlthtolths _ _ h) h0)).
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natlthchoice2 _ _ h1) as [h2|h2].
      { destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)). }
      { destruct h2; destruct (isirreflnatlth _ h0). }
    + destruct h1; simpl.
      rewrite <- (coconeInCommutes ccK i (S i) (idpath _)), assoc.
      unfold fun_lt.
      eapply pathscomp0.
      eapply cancel_postcomposition.
      apply BinProductOfArrows_comp.
      rewrite id_left, id_right.
      apply cancel_postcomposition, BinProductOfArrows_eq; trivial.
      simpl; destruct (natlehchoice4 i i h0) as [h1|h1]; [destruct (isirreflnatlth _ h1)|].
      apply maponpaths, maponpaths, isasetnat.
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natgehchoice i (S j) h0) as [h2|h2].
      { unfold fun_gt; rewrite assoc.
        eapply pathscomp0.
        eapply cancel_postcomposition.
        apply BinProductOfArrows_comp.
        rewrite id_right.
        apply cancel_postcomposition.
        apply BinProductOfArrows_eq; trivial.
        rewrite <- (chain_mor_commutes2 cAB _ _ h1 h2).
        apply idpath. }
      { destruct h.
        unfold fun_gt; simpl.
        generalize h1; clear h1.
        rewrite h2; intro h1.
        apply cancel_postcomposition.
        apply BinProductOfArrows_eq; trivial; simpl.
        destruct (natlehchoice4 j j h1); [destruct (isirreflnatlth _ h)|].
        apply maponpaths, maponpaths, isasetnat. }
    + destruct h1; destruct (negnatgehnsn _ h0).
Qed.

(* The cocone over K from the A_i * B chain *)
Lemma ccAiB_K (cAB : chain (binproduct_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) i :
  cocone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i)))
         (mapchain (pr2_functor C C) cAB)) K.
Proof.
simple refine (mk_cocone _ _).
+ intro j; apply (map_to_K cAB K ccK i j).
+ simpl; intros j k e; apply map_to_K_commutes.
Defined.

Section omega_cocont_binproduct.

Variable cAB : chain (binproduct_precategory C C).
Variable LM : C × C.
Variable ccLM : cocone cAB LM.
Variable HccLM : isColimCocone cAB LM ccLM.
Variable K : C.
Variable ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K.
Let L := pr1 LM : C.
Let M := pr2 LM : (λ _ : C, C) (pr1 LM).
Let cA := mapchain (pr1_functor C C) cAB : chain C.
Let cB := mapchain (pr2_functor C C) cAB : chain C.
Let HA := isColimCocone_pr1_functor _ _ hsC _ _ _ HccLM
  : isColimCocone cA L (cocone_pr1_functor C C cAB LM ccLM).
Let HB := isColimCocone_pr2_functor _ _ hsC _ _ _ HccLM
  : isColimCocone cB M (cocone_pr2_functor C C cAB LM ccLM).

(* Form the colimiting cocones of "A_i * B_0 -> A_i * B_1 -> ..." *)
Let HAiB :=
  fun i => is_omega_cocont_constprod_functor1 _ PC hsC hE (pr1 (pr1 cAB i)) _ _ _ HB.

(* Turn HAiB into a ColimCocone: *)
Let CCAiB := fun i => mk_ColimCocone _ _ _ (HAiB i).

(* Define the HAiM ColimCocone: *)
Let HAiM :=
  mk_ColimCocone _ _ _ (is_omega_cocont_constprod_functor2 _ PC hsC hE M _ _ _ HA).

Let ccAiB_K := fun i => ccAiB_K _ _ ccK i.

(* The f which is using in colimOfArrows *)
Local Definition f i j : C
   ⟦ BinProduct_of_functors_ob C C PC (constant_functor C C (pr1 (dob cAB i)))
       (functor_identity C) (pr2 (dob cAB j)),
   BinProduct_of_functors_ob C C PC (constant_functor C C (pr1 (dob cAB (S i))))
     (functor_identity C) (pr2 (dob cAB j)) ⟧.
Proof.
  apply BinProductOfArrows; [apply (dmor cAB (idpath _)) | apply identity ].
Defined.

Local Lemma fNat : Π i u v (e : edge u v),
   dmor (mapdiagram (constprod_functor1 PC _) cB) e ;; f i v =
   f i u ;; dmor (mapdiagram (constprod_functor1 PC _) cB) e.
Proof.
  intros i j k e; destruct e; simpl.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  eapply pathscomp0; [|eapply pathsinv0; apply BinProductOfArrows_comp].
  now rewrite !id_left, !id_right.
Qed.

(* Define the chain A_i * M *)
Local Definition AiM_chain : chain C.
Proof.
  mkpair.
  - intro i; apply (colim (CCAiB i)).
  - intros i j e; destruct e.
    apply (colimOfArrows (CCAiB i) (CCAiB (S i)) (f i) (fNat i)).
Defined.

Local Lemma AiM_chain_eq : Π i, dmor AiM_chain (idpath (S i)) =
                       dmor (mapdiagram (constprod_functor2 PC M) cA) (idpath _).
Proof.
  intro i; simpl; unfold colimOfArrows, BinProduct_of_functors_mor; simpl.
  apply pathsinv0, colimArrowUnique.
  simpl; intro j.
  unfold colimIn; simpl; unfold BinProduct_of_functors_mor, f; simpl.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  apply pathsinv0.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  now rewrite !id_left, !id_right.
Qed.

(* Define a cocone over K from the A_i * M chain *)
Local Lemma ccAiM_K_subproof : Π u v (e : edge u v),
   dmor (mapdiagram (constprod_functor2 PC M) cA) e ;;
   colimArrow (CCAiB v) K (ccAiB_K v) = colimArrow (CCAiB u) K (ccAiB_K u).
Proof.
  intros i j e; destruct e; simpl.
  generalize (AiM_chain_eq i); simpl; intro H; rewrite <- H; clear H; simpl.
  eapply pathscomp0.
  apply (precompWithColimOfArrows _ _ (CCAiB i) (CCAiB (S i)) _ _ K (ccAiB_K (S i))).
  apply (colimArrowUnique (CCAiB i) K (ccAiB_K i)).
  simpl; intros j.
  eapply pathscomp0; [apply (colimArrowCommutes (CCAiB i) K)|]; simpl.
  unfold map_to_K.
  destruct (natlthorgeh (S i) j).
  + destruct (natlthorgeh i j).
    * rewrite assoc; apply cancel_postcomposition.
      unfold f, fun_lt; simpl.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      now rewrite id_right, <- (chain_mor_commutes2 _ i j h0 h).
    * destruct (isasymmnatgth _ _ h h0).
  + destruct (natgehchoice (S i) j h).
    * destruct h.
      { destruct (natlthorgeh i j).
        - destruct (natlthchoice2 _ _ h) as [h2|h2].
          + destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)).
          + destruct h2; destruct (isirreflnatlth _ h0).
        - destruct (natgehchoice i j h).
          + destruct h.
            rewrite <- (coconeInCommutes ccK i _ (idpath _)); simpl.
            rewrite !assoc; apply cancel_postcomposition.
            unfold f, fun_gt.
            rewrite BinProductOfArrows_comp.
            eapply pathscomp0; [apply BinProductOfArrows_comp|].
            now rewrite !id_left, !id_right, (chain_mor_commutes3 cAB _ _ h0 h1).
          + destruct p.
            rewrite <- (coconeInCommutes ccK i _ (idpath _)), assoc.
            apply cancel_postcomposition.
            unfold f, fun_gt.
            eapply pathscomp0; [apply BinProductOfArrows_comp|].
            rewrite id_left, id_right.
            apply BinProductOfArrows_eq; trivial; simpl.
            destruct (natlehchoice4 i i h0); [destruct (isirreflnatlth _ h1)|].
            apply maponpaths, maponpaths, isasetnat.
       }
    * destruct p, h.
      destruct (natlthorgeh i (S i)); [|destruct (negnatgehnsn _ h)].
      apply cancel_postcomposition; unfold f, fun_lt.
      apply BinProductOfArrows_eq; trivial; simpl.
      destruct (natlehchoice4 i i h); [destruct (isirreflnatlth _ h0)|].
      assert (H : idpath (S i) = maponpaths S p). apply isasetnat.
      now rewrite H.
Qed.

Local Definition ccAiM_K := mk_cocone _ ccAiM_K_subproof.

Local Lemma is_cocone_morphism :
 Π v : nat,
   BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) ;;
   colimArrow HAiM K ccAiM_K = coconeIn ccK v.
Proof.
  intro i.
  generalize (colimArrowCommutes HAiM K ccAiM_K i).
  assert (H : coconeIn ccAiM_K i = colimArrow (CCAiB i) K (ccAiB_K i)).
  { apply idpath. }
  rewrite H; intros HH.
  generalize (colimArrowCommutes (CCAiB i) K (ccAiB_K i) i).
  rewrite <- HH; simpl; unfold map_to_K.
  destruct (natlthorgeh i i); [destruct (isirreflnatlth _ h)|].
  destruct (natgehchoice i i h); [destruct (isirreflnatgth _ h0)|].
  simpl; destruct h, p.
  intros HHH.
  rewrite <- HHH, assoc.
  apply cancel_postcomposition.
  unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
  apply pathsinv0.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  now rewrite id_left, id_right.
Qed.

Lemma is_unique_cocone_morphism : Π
   t : Σ x : C ⟦ BinProductObject C (PC L M), K ⟧,
       Π v : nat,
       BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
         (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) ;; x =
       coconeIn ccK v, t = colimArrow HAiM K ccAiM_K,, is_cocone_morphism.
Proof.
  intro t.
  apply subtypeEquality; simpl.
  + intro; apply impred; intros; apply hsC.
  + apply (colimArrowUnique HAiM K ccAiM_K).
    destruct t; simpl; intro i.
    apply (colimArrowUnique (CCAiB i) K (ccAiB_K i)).
    simpl; intros j; unfold map_to_K.
    destruct (natlthorgeh i j).
    * rewrite <- (p j); unfold fun_lt.
      rewrite !assoc.
      apply cancel_postcomposition.
      unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      apply pathsinv0.
      eapply pathscomp0; [apply BinProductOfArrows_comp|].
      rewrite !id_left, id_right.
      apply BinProductOfArrows_eq; trivial.
      apply (maponpaths pr1 (chain_mor_commutes cAB LM ccLM i j h)).
    * destruct (natgehchoice i j h).
      { unfold fun_gt; rewrite <- (p i), !assoc.
        apply cancel_postcomposition.
        unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        apply pathsinv0.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        now rewrite !id_left, id_right, <- (chain_mor_commutes cAB LM ccLM _ _ h0). }
      { destruct p0.
        rewrite <- (p i), assoc.
        apply cancel_postcomposition.
        unfold colimIn; simpl; unfold BinProduct_of_functors_mor; simpl.
        eapply pathscomp0; [apply BinProductOfArrows_comp|].
        now rewrite id_left, id_right. }
Qed.

Definition isColimProductOfColims :  ∃! x : C ⟦ BinProductObject C (PC L M), K ⟧,
   Π v : nat,
   BinProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) ;; x =
   coconeIn ccK v.
Proof.
mkpair.
- mkpair.
  + apply (colimArrow HAiM K ccAiM_K).
  + apply is_cocone_morphism.
- apply is_unique_cocone_morphism.
Defined.

End omega_cocont_binproduct.

Lemma is_omega_cocont_binproduct_functor : is_omega_cocont (binproduct_functor PC).
Proof.
intros cAB LM ccLM HccLM K ccK; simpl in *.
apply isColimProductOfColims.
apply HccLM.
Defined.

End binprod_functor.

Section BinProduct_of_functors.

Variables (C D : precategory) (PC : BinProducts C) (PD : BinProducts D) (hED : has_exponentials PD).
Variables (hsC : has_homsets C) (hsD : has_homsets D).

Lemma is_omega_cocont_BinProduct_of_functors_alt (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinProduct_of_functors_alt PD F G).
Proof.
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_bindelta_functor _ PC hsC).
apply (is_omega_cocont_functor_composite hsD).
  apply (is_omega_cocont_binproduct_pair_functor _ _ _ _ _ _ hsC hsC hsD hsD HF HG).
apply (is_omega_cocont_binproduct_functor _ _ hsD hED).
Defined.

Definition omega_cocont_BinProduct_of_functors_alt (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinProduct_of_functors_alt _ _ (pr2 F) (pr2 G)).

Lemma is_omega_cocont_BinProduct_of_functors (F G : functor C D)
  (HF : is_omega_cocont F) (HG : is_omega_cocont G) :
  is_omega_cocont (BinProduct_of_functors _ _ PD F G).
Proof.
exact (transportf _
        (BinProduct_of_functors_alt_eq_BinProduct_of_functors C D PD hsD F G)
        (is_omega_cocont_BinProduct_of_functors_alt _ _ HF HG)).
Defined.

Definition omega_cocont_BinProduct_of_functors (F G : omega_cocont_functor C D) :
  omega_cocont_functor C D :=
    tpair _ _ (is_omega_cocont_BinProduct_of_functors _ _ (pr2 F) (pr2 G)).

End BinProduct_of_functors.

(** Precomposition functor is cocontinuous *)
Section pre_composition_functor.

Variables M C A : precategory.
Variables (K : functor M C).
Variables (hsC : has_homsets C) (hsA : has_homsets A).
Variables (LA : Lims A).

Local Notation "c ↓ K" := (cComma hsC K c) (at level 30).

Section fix_T.

Variable (T : functor M A).

Local Definition Q (c : C) : functor (c ↓ K) M := cComma_pr1 hsC K c.

Local Definition QT (c : C) := functor_composite (Q c) T.

Local Definition R (c : C) := lim (LA _ (QT c)).

Local Definition lambda (c : C) : cone (QT c) (R c) := limCone (LA _ (QT c)).

Local Definition Rmor_cone (c c' : C) (g : C⟦c,c'⟧) : cone (QT c') (R c).
Proof.
use mk_cone.
- intro m1f1.
  transparent assert (m1gf1 : (c ↓ K)).
  { mkpair.
    + apply (pr1 m1f1).
    + apply (g ;; pr2 m1f1). }
  exact (coneOut (lambda c) m1gf1).
- intros x y f; simpl in *.
  transparent assert (e : ((c ↓ K) ⟦ pr1 x,, g ;; pr2 x, pr1 y,, g ;; pr2 y ⟧)).
  { mkpair.
    + apply (pr1 f).
    + now rewrite <- assoc; rewrite (pr2 f). }
  exact (coneOutCommutes (lambda c) _ _ e).
Defined.

Local Definition Rmor (c c' : C) (g : C⟦c,c'⟧) : A⟦R c,R c'⟧ :=
  limArrow (LA (c' ↓ K) (QT c')) (R c) (Rmor_cone c c' g).

Local Definition R_data : functor_data C A := R,,Rmor.
Local Lemma R_is_functor : is_functor R_data.
Proof.
split.
- intros c; simpl.
  apply pathsinv0, limArrowUnique.
  intro c'; simpl; rewrite !id_left.
  now destruct c'.
- intros c c' c'' f f'; simpl.
  apply pathsinv0, limArrowUnique; intros x; simpl.
  rewrite <- assoc; eapply pathscomp0.
  apply maponpaths, (limArrowCommutes _ _ (Rmor_cone c' c'' f')).
  eapply pathscomp0.
  apply (limArrowCommutes _ _ (Rmor_cone c c' f) (pr1 x,,f' ;; pr2 x)).
  destruct x.
  now rewrite <- assoc.
Qed.

Local Definition R_functor : functor C A := tpair _ R_data R_is_functor.

Local Definition eps_n (n : M) : A⟦R_functor (K n),T n⟧ :=
  coneOut (lambda (K n)) (n,,identity (K n)).

Local Definition Kid n : K n ↓ K := (n,, identity (K n)).

Local Lemma eps_is_nat_trans : is_nat_trans (functor_composite_data K R_data) T eps_n.
Proof.
intros n n' h; simpl.
eapply pathscomp0.
apply (limArrowCommutes (LA (K n' ↓ K) (QT (K n'))) (R (K n))
       (Rmor_cone (K n) (K n') (# K h)) (Kid n')).
unfold eps_n; simpl.
transparent assert (v : (K n ↓ K)).
{ apply (n',, # K h ;; identity (K n')). }
transparent assert (e : (K n ↓ K ⟦ Kid n, v ⟧)).
{ mkpair.
  + apply h.
  + abstract (now rewrite id_left, id_right).
}
now apply pathsinv0; eapply pathscomp0; [apply (coneOutCommutes (lambda (K n)) _ _ e)|].
Qed.

Local Definition eps : [M,A,hsA]⟦functor_composite K R_functor,T⟧ :=
  tpair _ eps_n eps_is_nat_trans.

End fix_T.

(** Construction of right Kan extensions based on MacLane, CWM, X.3 (p. 233) *)
Lemma RightKanExtension_from_limits : GlobalRightKanExtensionExists _ _ K _ hsC hsA.
Proof.
unfold GlobalRightKanExtensionExists.
use adjunction_from_partial.
- apply R_functor.
- apply eps.
- intros T S α; simpl in *.

  transparent assert (cc : (Π c, cone (QT T c) (S c))).
  { intro c.
    use mk_cone.
    + intro mf; apply (# S (pr2 mf) ;; α (pr1 mf)).
    + abstract (intros fm fm' h; simpl; rewrite <- assoc;
                eapply pathscomp0; [apply maponpaths, (pathsinv0 (nat_trans_ax α _ _ (pr1 h)))|];
                simpl; rewrite assoc, <- functor_comp; apply cancel_postcomposition, maponpaths, (pr2 h)).
  }

  transparent assert (σ : (Π c, A ⟦ S c, R T c ⟧)).
  { intro c; apply (limArrow _ _ (cc c)). }

  set (lambda' := fun c' mf' => limOut (LA (c' ↓ K) (QT T c')) mf').

  (* this is the conclusion from the big diagram (8) in MacLane's proof *)
  assert (H : Π c c' (g : C ⟦ c, c' ⟧) (mf' : c' ↓ K),
                # S g ;; σ c' ;; lambda' _ mf' = σ c ;; Rmor T c c' g ;; lambda' _ mf').
  { intros c c' g mf'.
    rewrite <- !assoc.
    apply pathsinv0; eapply pathscomp0.
    apply maponpaths, (limArrowCommutes _ _ (Rmor_cone T c c' g) mf').
    apply pathsinv0; eapply pathscomp0.
    eapply maponpaths, (limArrowCommutes _ _ (cc c') mf').
    simpl; rewrite assoc, <- functor_comp.
    set (mf := tpair _ (pr1 mf') (g ;; pr2 mf') : c ↓ K).
    apply pathsinv0.
    exact (limArrowCommutes (LA (c ↓ K) (QT T c)) (S c) (cc c) mf).
  }

  assert (is_nat_trans_σ : is_nat_trans S (R_data T) σ).
  { intros c c' g; simpl.
    transparent assert (ccc : (cone (QT T c') (S c))).
    { use mk_cone.
      - intro mf'; apply (σ c ;; Rmor T c c' g ;; limOut (LA (c' ↓ K) (QT T c')) mf').
      - abstract (intros u v e; simpl; rewrite <- !assoc;
                  apply maponpaths, maponpaths, (limOutCommutes (LA (c' ↓ K) (QT T c')) u v e)).
    }
    rewrite (limArrowUnique (LA (c' ↓ K) (QT T c')) _ ccc (# S g ;; σ c') (H _ _ _)).
    now apply pathsinv0, limArrowUnique.
  }

  mkpair.
  + apply (tpair _ (tpair _ σ is_nat_trans_σ)).
    apply (nat_trans_eq hsA); intro n; cbn.
    generalize (limArrowCommutes (LA (K n ↓ K) (QT T (K n))) _ (cc _) (Kid n)); simpl.
    now rewrite functor_id, id_left.
  + intro x.
    apply subtypeEquality; [intros xx; apply (isaset_nat_trans hsA)|].
    apply subtypeEquality; [intros xx; apply (isaprop_is_nat_trans _ _ hsA)|]; simpl.
    apply funextsec; intro c.
    apply limArrowUnique; intro u; simpl.
    destruct x as [t p]; simpl.
    assert (temp : α (pr1 u) = nat_trans_comp _ _ T (pre_whisker K t) (eps T) (pr1 u)).
      now rewrite p.
    rewrite temp; simpl.
    destruct u as [n g]; simpl in *.
    apply pathsinv0; eapply pathscomp0;
    [rewrite assoc; apply cancel_postcomposition, (nat_trans_ax t _ _ g)|].
    rewrite <- !assoc; apply maponpaths.
    generalize (limArrowCommutes (LA (K n ↓ K) _) _ (Rmor_cone T c (K n) g) (Kid n)).
    now simpl; rewrite id_right.
Defined.

Lemma cocont_pre_composition_functor :
  is_cocont (pre_composition_functor _ _ _ hsC hsA K).
Proof.
apply left_adjoint_cocont.
- apply RightKanExtension_from_limits.
- apply functor_category_has_homsets.
- apply functor_category_has_homsets.
Qed.

Lemma is_omega_cocont_pre_composition_functor :
  is_omega_cocont (pre_composition_functor _ _ _ hsC hsA K).
Proof.
intros c L ccL.
apply cocont_pre_composition_functor.
Defined.

Definition omega_cocont_pre_composition_functor :
  omega_cocont_functor [C, A, hsA] [M, A, hsA] :=
  tpair _ _ is_omega_cocont_pre_composition_functor.

End pre_composition_functor.

End cocont_functors.

(** Specialized notations for HSET *)
Delimit Scope cocont_functor_hset_scope with CS.

Notation "' x" := (omega_cocont_constant_functor _ _ has_homsets_HSET x)
                    (at level 10) : cocont_functor_hset_scope.

Notation "'Id'" := (omega_cocont_functor_identity _ has_homsets_HSET) :
                     cocont_functor_hset_scope.

Notation "F * G" :=
  (omega_cocont_BinProduct_of_functors_alt _ _ BinProductsHSET _
     has_exponentials_HSET has_homsets_HSET has_homsets_HSET F G) :
    cocont_functor_hset_scope.

Notation "F + G" :=
  (omega_cocont_BinCoproduct_of_functors_alt _ _ BinProductsHSET BinCoproductsHSET
     has_homsets_HSET has_homsets_HSET F G) : cocont_functor_hset_scope.

(* omega_cocont_coproduct_functor has worse computational behavior
   than omega_cocont_coproduct_of_functors and breaks
   isalghom_pr1foldr in lists *)
(* Notation "F + G" := *)
(*   (omega_cocont_coproduct_functor _ _ ProductsHSET CoproductsHSET *)
(*      has_homsets_HSET has_homsets_HSET _ _ (pr2 F) (pr2 G)) : *)
(*     cocont_functor_hset_scope. *)

Notation "1" := (unitHSET) : cocont_functor_hset_scope.
Notation "0" := (emptyHSET) : cocont_functor_hset_scope.
