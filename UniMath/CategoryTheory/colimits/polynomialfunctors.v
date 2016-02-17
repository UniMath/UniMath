Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.colimits.chains.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).

(* Proofs that various polynomial functors are omega cocontinuous *)
Section polynomial_functors.

Variables (C : precategory) (hsC : has_homsets C).

(* The constant functor is omega cocontinuous *)
Section constant_functor.

Variable (x : C).

Lemma omega_cocontConstantFunctor : omega_cocont (constant_functor C C x).
Proof.
intros c L ccL HcL y ccy; simpl.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + apply (coconeIn ccy 0).
  + simpl; intro n; rewrite id_left.
    destruct ccy as [f Hf]; simpl in *.
    induction n; [apply idpath|].
    now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left.
- simpl; intro p; apply subtypeEquality.
  + intros f; apply impred; intro; apply hsC.
  + now simpl; destruct p as [p H]; rewrite <- (H 0), id_left.
Defined.

End constant_functor.

(* The identity functor is omega cocontinuous *)
Section identity_functor.

Lemma omega_cocontFunctorIdentity : omega_cocont (functor_identity C).
Proof.
intros c L ccL HcL.
apply (preserves_colimit_identity hsC _ _ _ HcL).
Defined.

End identity_functor.

(* Functor composition preserves omega cocontinuity *)
Section functor_comp.

Lemma omega_cocontFunctorComposite (F G : functor C C) :
  omega_cocont F -> omega_cocont G -> omega_cocont (functor_composite _ _ _ F G).
Proof.
intros hF hG c L cc.
apply (preserves_colimit_comp hsC); [apply hF|apply hG].
Defined.

End functor_comp.

(* The functor "x * F" is omega_cocont. This is only proved for set at the
   moment as it needs that the category is cartesian closed *)
Section constprod_functor.

Variables (x : HSET).

Definition constprod_functor : functor HSET HSET :=
  product_functor HSET HSET ProductsHSET (constant_functor HSET HSET x) (functor_identity HSET).

Definition flip {A B C : UU} (f : A -> B -> C) : B -> A -> C := fun x y => f y x.

Lemma omega_cocontConstProdFunctor : omega_cocont constprod_functor.
Proof.
intros hF c L ccL HcL cc.
destruct cc as [f hf]; simpl in *; unfold product_functor_ob in *; simpl in *.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + apply uncurry, flip.
    apply (@colimArrow _ _ _ (mk_ColimCocone _ _ _ ccL) (hset_fun_space x HcL)).
    simple refine (mk_cocone _ _).
    * simpl; intro n; apply flip, curry, f.
    * abstract (simpl; intros m n e; rewrite <- (hf m n e); destruct e; simpl;
                repeat (apply funextfun; intro); apply idpath).
  + intro n.
    apply funextfun; intro p.
    assert (peta : p = (pr1 p,, pr2 p)).
      destruct p; apply idpath.
    rewrite peta.
    generalize (colimArrowCommutes (mk_ColimCocone hF c L ccL) _
                 (mk_cocone _ (omega_cocontConstProdFunctor_subproof x hF c L ccL HcL f hf)) n).
    unfold flip, curry, colimIn; simpl.
    intro H.
    now rewrite <- (toforallpaths _ _ _ (toforallpaths _ _ _ H (pr2 p)) (pr1 p)).
- intro p.
  unfold uncurry; simpl.
  apply subtypeEquality; simpl.
  + intro g; apply impred; intro t.
    simple refine (let ff : HSET ⟦(x × dob hF t)%set,HcL⟧ := _ in _).
    * simpl; apply f.
    * apply (@has_homsets_HSET _ HcL _ ff).
  + destruct p as [t p]; simpl.
    apply funextfun; intro xc; destruct xc as [x' c']; simpl.
    simple refine (let g : HSET⟦colim (mk_ColimCocone hF c L ccL),
                                hset_fun_space x HcL⟧ := _ in _).
    * simpl; apply flip, curry, t.
    * rewrite <- (colimArrowUnique _ _ _ g); [apply idpath | ].
      now intro n; simpl; rewrite <- (p n).
Defined.

End constprod_functor.

(* The functor "x + F" is omega_cocont. Assumes that the category has coproducts *)
Section constcoprod_functor.

Variables (x : C) (PC : Coproducts C).

Definition constcoprod_functor : functor C C :=
  coproduct_functor C C PC (constant_functor C C x) (functor_identity C).

Lemma omega_cocontConstCoprodFunctor : omega_cocont constcoprod_functor.
Proof.
intros hF c L ccL HcL cc.
destruct cc as [f hf]; simpl in *; unfold coproduct_functor_ob in *; simpl in *.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + eapply CoproductArrow.
    * exact (CoproductIn1 _ (PC x (dob hF 0)) ;; f 0).
    * simple refine (let ccHcL : cocone hF HcL := _ in _).
      { simple refine (mk_cocone _ _).
        - intros n; exact (CoproductIn2 _ (PC x (dob hF n)) ;; f n).
        - abstract (
            intros m n e; destruct e; simpl;
            rewrite <- (hf m _ (idpath _)), !assoc; apply cancel_postcomposition;
            now unfold coproduct_functor_mor; simpl; rewrite CoproductOfArrowsIn2). }
      apply (pr1 (pr1 (ccL HcL ccHcL))).
  + simpl; intro n; unfold coproduct_functor_mor in *.
    rewrite precompWithCoproductArrow.
    apply pathsinv0, CoproductArrowUnique.
    * rewrite id_left; induction n; [apply idpath|].
      now rewrite <- IHn, <- (hf n _ (idpath _)), assoc, CoproductOfArrowsIn1, id_left.
    * rewrite <- (hf n _ (idpath _)).
      destruct ccL; destruct t; simpl in *.
      rewrite p0; apply maponpaths, hf.
- intro t; apply subtypeEquality; simpl.
  + intro g; apply impred; intro; apply hsC.
  + destruct t; destruct ccL; unfold coproduct_functor_mor in *.
    destruct t0; simpl.
    apply CoproductArrowUnique.
    * now rewrite <- (p 0), assoc, CoproductOfArrowsIn1, id_left.
    * simple refine (let temp : Σ x0 : C ⟦ c, HcL ⟧, ∀ v : nat,
         coconeIn L v ;; x0 = CoproductIn2 C (PC x (dob hF v)) ;; f v := _ in _).
        { apply (tpair _ (CoproductIn2 C (PC x c) ;; t)).
          now intro n; rewrite <- (p n), !assoc, CoproductOfArrowsIn2. }
      apply (maponpaths pr1 (p0 temp)).
Defined.

End constcoprod_functor.

End polynomial_functors.

(* Lists as the colimit of a chain given by the list functor: F(X) = 1 + A * X *)
Section lists.

Variable A : HSET.

(* F(X) = A * X *)
Definition stream : functor HSET HSET := constprod_functor A.

(* F(X) = 1 + (A * X) *)
Definition listFunctor : functor HSET HSET :=
  functor_composite _ _ _ stream (constcoprod_functor _ unitHSET CoproductsHSET).

Lemma omega_cocont_listFunctor : omega_cocont listFunctor.
Proof.
apply (omega_cocontFunctorComposite _ has_homsets_HSET).
- apply omega_cocontConstProdFunctor.
- apply (omega_cocontConstCoprodFunctor _ has_homsets_HSET).
Defined.

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg listFunctor has_homsets_HSET).
Proof.
apply (colimAlgInitial _ _ _ omega_cocont_listFunctor InitialHSET (ColimCoconeHSET _ _)).
Defined.

Definition List : HSET :=
  colim (ColimCoconeHSET nat_graph (initChain InitialHSET listFunctor)).
Let List_mor : HSET⟦listFunctor List,List⟧ :=
  alg_map _ (InitialObject listFunctor_Initial).
Let List_alg : algebra_ob listFunctor :=
  InitialObject listFunctor_Initial.

Definition nil_map : HSET⟦unitHSET,List⟧.
Proof.
simpl; intro x.
apply List_mor, inl, x.
Defined.

Definition nil : pr1 List := nil_map tt.

Definition cons_map : HSET⟦(A × List)%set,List⟧.
Proof.
intros xs.
apply List_mor, (inr xs).
Defined.

Definition cons : pr1 A × pr1 List -> pr1 List := cons_map.

(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       foldr x f : List A -> X *)

Definition mk_listAlgebra (X : HSET) (x : pr1 X) (f : HSET⟦(A × X)%set,X⟧) : algebra_ob listFunctor.
Proof.
set (x' := λ (_ : unit), x).
apply (tpair (fun X1 : hSet => unit ⨿ (pr1 A × X1) → X1) X (sumofmaps x' f) : algebra_ob listFunctor).
Defined.

Definition foldr_map (X : HSET) (x : pr1 X) (f : HSET⟦(A × X)%set,X⟧) :
  algebra_mor _ List_alg (mk_listAlgebra X x f).
Proof.
apply (InitialArrow listFunctor_Initial (mk_listAlgebra X x f)).
Defined.

Definition foldr (X : HSET) (x : pr1 X)
  (f : pr1 A × pr1 X -> pr1 X) : pr1 List -> pr1 X.
Proof.
apply (foldr_map _ x f).
Defined.

(* Maybe quantify over "λ _ : unit, x" instead of nil? *)
Lemma foldr_nil (X : hSet) (x : X) (f : pr1 A × X -> X) : foldr X x f nil = x.
Proof.
assert (F := maponpaths (fun x => CoproductIn1 _ _ ;; x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x f))).
apply (toforallpaths _ _ _ F tt).
Qed.

Lemma foldr_cons (X : hSet) (x : X) (f : pr1 A × X -> X) (a : pr1 A) (l : pr1 List) :
  foldr X x f (cons (a,,l)) = f (a,,foldr X x f l).
Proof.
assert (F := maponpaths (fun x => CoproductIn2 _ _ ;; x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x f))).
assert (Fal := toforallpaths _ _ _ F (a,,l)).
clear F.
(* apply foo. *) (* This doesn't work here. why? *)
unfold compose in Fal.
simpl in Fal.
apply Fal.
Qed. (* This Qed is slow! *)

(* This defines the induction principle for lists using foldr *)
Section list_induction.

(* TODO: P should not return an hSet but be split into two things *)
Variable (P : pr1 List -> hSet).
Variables (P0 : P nil) (Pc : forall (a : pr1 A) (l : pr1 List), P l -> P (cons (a,,l))).

Let P' : UU := Σ l, P l.
Let P0' : P' := (nil,, P0).
Let Pc' : pr1 A × P' -> P' :=
  λ ap : pr1 A × P', cons (pr1 ap,, pr1 (pr2 ap)),,Pc (pr1 ap) (pr1 (pr2 ap)) (pr2 (pr2 ap)).

Definition P'HSET : HSET.
Proof.
apply (tpair _ P').
abstract (apply (isofhleveltotal2 2); [apply setproperty | intros x; apply setproperty ]).
Defined.

Lemma isalghom_pr1foldr :
  is_algebra_mor _ List_alg List_alg (fun l => pr1 (foldr P'HSET P0' Pc' l)).
Proof.
apply CoproductArrow_eq_cor.
- apply funextfun; intro x; destruct x; apply idpath.
- apply funextfun; intro x; destruct x as [a l].
  apply (maponpaths pr1 (foldr_cons P'HSET P0' Pc' a l)).
Qed.

Definition pr1foldr_algmor : algebra_mor _ List_alg List_alg := tpair _ _ isalghom_pr1foldr.

Lemma pr1foldr_algmor_identity : identity _ = pr1foldr_algmor.
Proof.
now rewrite <- (InitialEndo_is_identity _ listFunctor_Initial pr1foldr_algmor).
Qed.

Lemma listInd l : P l.
Proof.
assert (H : pr1 (foldr P'HSET P0' Pc' l) = l).
  apply (toforallpaths _ _ _ (!pr1foldr_algmor_identity) l).
rewrite <- H.
apply (pr2 (foldr P'HSET P0' Pc' l)).
Defined.

End list_induction.

Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Definition natHSET : HSET.
Proof.
exists nat.
abstract (apply isasetnat).
Defined.

(* TODO: separate X from isaset X *)
Definition length : pr1 List -> nat :=
  foldr natHSET 0 (fun x => S (pr2 x)).

Definition map (f : pr1 A -> pr1 A) : pr1 List -> pr1 List :=
  foldr _ nil (λ xxs : pr1 A × pr1 List, cons (f (pr1 xxs),, pr2 xxs)).

Lemma length_map (f : pr1 A -> pr1 A) (xs : pr1 List) : length (map f xs) = length xs.
Proof.
simple refine (let P : pr1 List -> hSet := _ in _).
  { intros l; mkpair.
    - apply (length (map f l) = length l).
    - apply isasetaprop, isasetnat. }
apply (listInd P).
- apply idpath.
- simpl; unfold map, length; simpl; intros a l Hl.
  now rewrite !foldr_cons, <- Hl.
Qed.

End lists.

(* Some examples of computations with lists over nat *)
Section nat_examples.

Definition testlist : pr1 (List natHSET) :=
  cons natHSET (5,, cons natHSET (2,, nil natHSET)).

Definition testlistS : pr1 (List natHSET) :=
  map natHSET (fun x => S x) testlist.

Definition sum : pr1 (List natHSET) -> nat :=
  foldr natHSET natHSET 0 (fun xy => pr1 xy + pr2 xy).

Eval vm_compute in length _ (nil natHSET).
Eval vm_compute in length _ testlist.
Eval vm_compute in length _ testlistS.
Eval vm_compute in sum testlist.
Eval vm_compute in sum testlistS.

Goal (forall l, length _ (cons natHSET (2,, l)) = S (length _ l)).
simpl.
intro l.
simpl.
cbn.
try apply idpath.
Abort.

(* Time Eval vm_compute in nil natHSET. *) (* This crashes my computer by using up all memory *)

End nat_examples.