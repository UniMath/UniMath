(************************************************************
      Benedikt Ahrens and Anders Mörtberg, October 2015
*************************************************************)

(** *********************************************************

Contents :

   Definition of chains of endofunctors

   Construction of the initial algebra of the initial chain

*************************************************************)

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

Local Notation "# F" := (functor_on_morphisms F) (at level 3).

Section move_upstream.

(* Move to limits.initial *)

Fixpoint iter_functor {C : precategory} (F : functor C C) (n : nat) : functor C C := match n with
  | O => functor_identity C
  | S n' => functor_composite _ _ _ (iter_functor F n') F
  end.

(* TODO : state this for any object and morphism, that is,
+   - Id^n a = a
+   - #(Id^n) f = f
+   thus avoiding use of funext
+
+  TODO: similar for
+   - (G o F)^n (a) = G^n(a) o F^n(a)
+   - #(G o F)^n (f) = #G^n(f) o #F^n(f)
+
*)

End move_upstream.

(* Local Notation "F ^ n" := (iter_functor _ F n) (at level 10, format "F ^ n"). *)

Section chains.

(* Define the chain:

     0 --> 1 --> 2 --> 3 --> ...

   with exactly one arrow from n to S n.
*)
Definition nat_graph : graph :=
  tpair (λ D : UU, D → D → UU) nat (λ m n, S m = n).

Local Notation "'chain'" := (diagram nat_graph).

Definition mapchain {C D : precategory} (F : functor C D)
  (c : chain C) : chain D := mapdiagram F c.

(* Construct the chain:

         !          F!            F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Definition initChain {C : precategory} (InitC : Initial C) (F : functor C C) : chain C.
Proof.
exists (λ n, iter_functor F n InitC).
intros m n Hmn; destruct Hmn; simpl.
induction m; simpl.
- exact (InitialArrow InitC _).
- exact (# F IHm).
Defined.

End chains.

Notation "'chain'" := (diagram nat_graph).

Definition omega_cocont {C D : precategory} (F : functor C D) : UU :=
  forall (c : chain C) (L : C) (cc : cocone c L),
  preserves_colimit F c L cc.

(* This section proves that (L,α : F L -> L) is the initial algebra
   where L is the colimit of the inital chain:

         !          F !           F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Section colim_initial_algebra.

Variables (C : precategory) (hsC : has_homsets C).
Variables (F : functor C C) (HF : omega_cocont F).
Variables (InitC : Initial C).

Let Fchain : chain C := initChain InitC F.

Variable (CC : ColimCocone Fchain).

Let L : C := colim CC.
Let FFchain : chain C := mapchain F Fchain.

Let Fa : cocone FFchain (F L) := mapcocone F _ (colimCocone CC).
Let FHC' : isColimCocone FFchain (F L) Fa :=
  HF Fchain L (colimCocone CC) (isColimCocone_from_ColimCocone CC).
Let FHC : ColimCocone FFchain := mk_ColimCocone _ _ _ FHC'.

Definition shiftCocone : cocone FFchain L.
Proof.
simple refine (mk_cocone _ _).
- intro n; apply (coconeIn (colimCocone CC) (S n)).
- intros m n e; destruct e.
  apply (coconeInCommutes (colimCocone CC) (S m) _ (idpath _)).
Defined.

Definition unshiftCocone (x : C) : cocone FFchain x -> cocone Fchain x.
Proof.
intros cc.
simple refine (mk_cocone _ _).
- simpl; intro n.
  destruct n as [|n]; simpl.
  + apply InitialArrow.
  + apply (coconeIn cc _).
- simpl; intros m n e; destruct e; simpl.
  destruct m as [|m].
  + apply InitialArrowUnique.
  + apply (coconeInCommutes cc m _ (idpath _)).
Defined.

Definition shiftIsColimCocone : isColimCocone FFchain L shiftCocone.
Proof.
intros x cc; simpl.
simple refine (tpair _ _ _).
+ simple refine (tpair _ _ _).
  * apply colimArrow, (unshiftCocone _ cc).
  * simpl; intro n.
    apply (colimArrowCommutes CC x (unshiftCocone x cc) (S n)).
+ simpl; intros p.
  apply subtypeEquality.
  * intro f; apply impred; intro; apply hsC.
  * apply colimArrowUnique; simpl; intro n.
    destruct n as [|n]; [ apply InitialArrowUnique | apply (pr2 p) ].
Defined.

Definition shiftColimCocone : ColimCocone FFchain :=
  mk_ColimCocone FFchain L shiftCocone shiftIsColimCocone.

Definition α_mor : C⟦F L,L⟧ := colimArrow FHC L shiftCocone.

Definition is_iso_α_mor : is_iso α_mor :=
  isColim_is_iso _ FHC _ _ shiftIsColimCocone.

Let α : iso (F L) L := isopair _ is_iso_α_mor.
Let α_inv : iso L (F L) := iso_inv_from_iso α.
Let α_alg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L α.

(* Why does this not compute? *)
Lemma unfold_inv_from_iso_α :
  inv_from_iso α = colimArrow shiftColimCocone _ (colimCocone FHC).
Proof.
cbn.
apply id_right.
Qed.

(* Given an algebra:

          a
   F A ------> A

 we now define an algebra morphism ad:

          α
   F L ------> L
    |          |
    |          | ad
    |          |
    V     a    V
   F A ------> A


*)
Section algebra_mor.

Variable (Aa : algebra_ob F).

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

Definition cocone_over_alg (n : nat) : C ⟦ dob Fchain n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn ;; a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

(* This makes Coq not unfold dmor during simpl *)
Arguments dmor : simpl never.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor Fchain e ;; an Sn = an n.
Proof.
destruct e.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- simpl; rewrite assoc.
  apply cancel_postcomposition, pathsinv0.
  eapply pathscomp0; [|simpl; apply functor_comp].
  now apply maponpaths, pathsinv0, IHn.
Qed.

(* ad = a† = a dagger *)
Definition ad : C⟦L,A⟧.
Proof.
apply colimArrow.
simple refine (mk_cocone _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma ad_is_algebra_mor : is_algebra_mor _ α_alg Aa ad.
Proof.
apply pathsinv0, iso_inv_to_left, colimArrowUnique; simpl; intro n.
destruct n as [|n].
- now apply InitialArrowUnique.
- rewrite assoc, unfold_inv_from_iso_α.
  eapply pathscomp0;
    [apply cancel_postcomposition, (colimArrowCommutes shiftColimCocone)|].
  simpl; rewrite assoc, <- functor_comp.
  apply cancel_postcomposition, maponpaths, (colimArrowCommutes CC).
Qed.

Definition ad_mor : algebra_mor F α_alg Aa := tpair _ _ ad_is_algebra_mor.

End algebra_mor.

Lemma temp (Aa : FunctorAlg F hsC) (Fa' : algebra_mor F α_alg Aa) : Fa' = ad_mor Aa.
Proof.
apply (algebra_mor_eq _ hsC); simpl.
apply colimArrowUnique; simpl; intro n.
destruct Fa' as [f hf]; simpl.
unfold is_algebra_mor in hf; simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  apply cancel_postcomposition, pathsinv0, (iso_inv_to_right _ _ _ _ _ α).
  rewrite unfold_inv_from_iso_α; apply pathsinv0.
  now eapply pathscomp0; [apply (colimArrowCommutes shiftColimCocone)|].
Qed.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) α_alg.
Proof.
apply mk_isInitial.
intros Aa.
exists (ad_mor Aa).
apply temp.
Defined.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  mk_Initial _ colimAlgIsInitial.

End colim_initial_algebra.

(* "good" functors *)
(* TODO: remove *)
Let good {C} F := @omega_cocont C C F.

Section polynomial_functors.

Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Variables (C : precategory) (hsC : has_homsets C).

(* TODO: Prove that polynomial functors are good *)
(* good(F), good(G) |- good(F * G) *)
(* good(F), good(G) |- good(F + G) *)
(*                  |- good(constant_functor A) *)
(*                  |- good(identity_functor) *)

Section constant_functor.

Variable (x : C).

Let Fx : functor C C := constant_functor C C x.

Lemma goodConstantFunctor : good Fx.
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

Section identity_functor.

Let Fid : functor C C := functor_identity C.

Lemma goodFunctorIdentity : good Fid.
Proof.
intros c L ccL HcL.
apply (preserves_colimit_identity hsC _ _ _ HcL).
Defined.

End identity_functor.

Section functor_comp.

(* preserves_colimit_comp  *)

Lemma goodFunctorComposite (F G : functor C C) :
  good F -> good G -> good (functor_composite _ _ _ F G).
Proof.
intros hF hG c L cc.
apply (preserves_colimit_comp hsC); [apply hF|apply hG].
Defined.

End functor_comp.

(* (* The functor "x * F" is good *) *)
(* Section constprod_functor. *)

(* (* TODO: This needs that C is cartesian closed *) *)
(* Variables (x : C) (* (F : functor C C)  *)(PC : Products C). *)

(* (* Definition constprod_functor : functor C C := *) *)
(* (*   product_functor C C PC (constant_functor C C x) F. *) *)

(* Definition constprod_functor : functor C C := *)
(*   product_functor C C PC (constant_functor C C x) (functor_identity C). *)

(* Lemma goodConstProdFunctor : good constprod_functor. *)
(* Proof. *)
(* Admitted. *)

(* End constprod_functor. *)

(* The functor "x * F" is good. This is only proved for set at the
   moment as it needs that the category is cartesian closed *)
Section constprod_functor.

Variables (x : HSET).

Definition constprod_functor : functor HSET HSET :=
  product_functor HSET HSET ProductsHSET (constant_functor HSET HSET x) (functor_identity HSET).

Definition flip {A B C : UU} (f : A -> B -> C) : B -> A -> C := fun x y => f y x.

(* Is this in the library? *)
(* This is toforallpaths *)
Lemma congr2 {A B D : UU} (f g : A -> B -> D) : f = g -> forall a b, f a b = g a b.
Proof.
now intro H; rewrite H.
Defined.

Lemma goodConstProdFunctor : good constprod_functor.
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
                 (mk_cocone _ (goodConstProdFunctor_subproof x hF c L ccL HcL f hf)) n).
    unfold flip, curry, colimIn; simpl.
    intro H; rewrite <- (congr2 _ _ H (pr2 p) (pr1 p)); apply idpath.
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

(* The functor "x + F" is good *)
Section constcoprod_functor.

Variables (x : C) (PC : Coproducts C).

Definition constcoprod_functor : functor C C :=
  coproduct_functor C C PC (constant_functor C C x) (functor_identity C).

Lemma goodConstCoprodFunctor : good constcoprod_functor.
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

Section lists.

Variable A : HSET.

(* F(X) = A * X *)
Definition stream : functor HSET HSET := constprod_functor A.

(* F(X) = 1 + (A * X) *)
Definition list_sig : functor HSET HSET :=
  functor_composite _ _ _ stream (constcoprod_functor _ unitHSET CoproductsHSET).

(* Arguments list : simpl never. *)

Lemma goodListSig : good list_sig.
Proof.
apply (goodFunctorComposite _ has_homsets_HSET).
  apply goodConstProdFunctor.
apply (goodConstCoprodFunctor _ has_homsets_HSET).
Defined.

Lemma list_sig_Initial :
  Initial (precategory_FunctorAlg list_sig has_homsets_HSET).
Proof.
apply (colimAlgInitial _ _ _ goodListSig InitialHSET (ColimCoconeHSET _ _)).
Defined.

(* Definition α_mor : C⟦F L,L⟧ := colimArrow FHC L shiftCocone. *)

(* Definition is_iso_α_mor : is_iso α_mor := *)
(*   isColim_is_iso _ FHC _ _ shiftIsColimCocone. *)

(* Let α : iso (F L) L := isopair _ is_iso_α_mor. *)
(* Let α_inv : iso L (F L) := iso_inv_from_iso α. *)
(* Let α_alg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L α. *)

Definition List : HSET := colim (ColimCoconeHSET nat_graph (initChain InitialHSET list_sig)).
Let β_mor : HSET⟦list_sig List,List⟧ := α_mor _ _ goodListSig InitialHSET (ColimCoconeHSET _ _).
(* Let β : iso (list L) L := isopair _ (is_iso_α_mor _ has_homsets_HSET _ goodList InitialHSET (ColimCoconeHSET _ _)). *)
(* Let β_inv : iso L (list L) := iso_inv_from_iso β. *)
(* Let β_alg : algebra_ob list := tpair (λ X : HSET, HSET ⟦ list X, X ⟧) L β. *)
Let List_alg : algebra_ob list_sig := InitialObject list_sig_Initial.


Let bd := (ad _ list_sig InitialHSET (ColimCoconeHSET _ _)).

Definition nil_map : HSET⟦unitHSET,List⟧.
Proof.
simpl; intro x.
apply β_mor, inl, x.
Defined.

Definition nil : pr1 List.
Proof.
exact (nil_map tt).
Defined.

Definition cons_map : HSET⟦(A × List)%set,List⟧.
Proof.
intros xs.
apply β_mor, (inr xs).
Defined.

Definition cons : pr1 A × pr1 List -> pr1 List.
Proof.
exact cons_map.
Defined.

(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       iter x f : List A -> X *)

Definition mk_listAlgebra (X : HSET) (x : pr1 X) (f : HSET⟦(A × X)%set,X⟧) : algebra_ob list_sig.
Proof.
set (x' := λ (_ : unit), x).
apply (tpair (fun X1 : hSet => unit ⨿ (pr1 A × X1) → X1) X (sumofmaps x' f) : algebra_ob list_sig).
Defined.

Definition iter_map (X : HSET) (x : pr1 X) (f : HSET⟦(A × X)%set,X⟧) : algebra_mor _ List_alg (mk_listAlgebra X x f).
Proof.
apply (InitialArrow list_sig_Initial (mk_listAlgebra X x f)).
Defined.

Definition iter (X : HSET) (x : pr1 X) (f : pr1 A × pr1 X -> pr1 X) : pr1 List -> pr1 X.
Proof.
apply (iter_map _ x f).
Defined.

Definition iter_map_bd (X : HSET) (x : pr1 X) (f : HSET⟦(A × X)%set,X⟧) : algebra_mor _ List_alg (mk_listAlgebra X x f).
(* HSET⟦List,X⟧. *)
Proof.
mkpair.
- apply (bd (mk_listAlgebra X x f)).
- admit.
Admitted.

Definition iter_bd (X : HSET) (x : pr1 X) (f : pr1 A × pr1 X -> pr1 X) : pr1 List -> pr1 X.
Proof.
apply (iter_map_bd _ x f).
Defined.

(* Maybe quantify over "λ _ : unit, x" instead of nil? *)
Lemma iter_nil (X : hSet) (x : X) (f : pr1 A × X -> X) : iter X x f nil = x.
Proof.
assert (bla := maponpaths (fun x => CoproductIn1 _ _ ;; x) (algebra_mor_commutes _ _ _ (iter_map X x f))).
apply (toforallpaths _ _ _ bla tt).
Qed.

Lemma iter_cons (X : hSet) (x : X) (f : pr1 A × X -> X) (a : pr1 A) (l : pr1 List) :
  iter X x f (cons (a,,l)) = f (a,,iter X x f l).
Proof.
assert (bla := maponpaths (fun x => CoproductIn2 _ _ ;; x) (algebra_mor_commutes _ _ _ (iter_map X x f))).
assert (foo := toforallpaths _ _ _ bla (a,,l)).
clear bla.
(* apply foo. *) (* This doesn't work here. why? *)
unfold compose in foo.
simpl in foo.
apply foo.
Qed.

(* Maybe quantify over "λ _ : unit, x" instead of nil? *)
Lemma iter_nil_bd (X : hSet) (x : X) (f : pr1 A × X -> X) : iter_bd X x f nil = x.
Proof.
assert (bla := maponpaths (fun x => CoproductIn1 _ _ ;; x) (algebra_mor_commutes _ _ _ (iter_map_bd X x f))).
apply (toforallpaths _ _ _ bla).
Qed.

Lemma iter_cons_bd (X : hSet) (x : X) (f : pr1 A × X -> X) (a : pr1 A) (l : pr1 List) :
  iter_bd X x f (cons (a,,l)) = f (a,,iter_bd X x f l).
Proof.
assert (bla := maponpaths (fun x => CoproductIn2 _ _ ;; x) (algebra_mor_commutes _ _ _ (iter_map_bd X x f))).
apply (toforallpaths _ _ _ bla (a,,l)).
Qed.

Section ind.

Variable (P : pr1 List -> hSet).
Variables (P0 : P nil) (Pc : forall (a : pr1 A) (l : pr1 List), P l -> P (cons (a,,l))).

Let P' : UU := Σ l, P l.
Let P0' : P' := (nil,, P0).
Let Pc' : pr1 A × P' -> P'.
intros ap.
mkpair.
- apply (cons (pr1 ap,,pr1 (pr2 ap))).
- exact (Pc (pr1 ap) (pr1 (pr2 ap)) (pr2 (pr2 ap))).
Defined.

Definition P'HSET : HSET.
Proof.
apply (tpair _ P').
unfold P'.
apply (isofhleveltotal2 2).
apply setproperty.
intros x.
apply setproperty.
Defined.

Definition auxInd : pr1 List -> pr1 P'HSET.
Proof.
apply iter_bd.
apply P0'.
apply Pc'.
Defined.

Definition pr1iter : HSET⟦List,List⟧.
Proof.
intros x.
exact (pr1 (auxInd x)).
Defined.

Lemma isalghom_pr1iter : is_algebra_mor _ List_alg List_alg pr1iter.
Proof.
unfold is_algebra_mor.
apply CoproductArrow_eq_cor.
-
apply funextfun; intro x.
unfold compose.
simpl.
destruct x.
simpl.
cbn.
unfold pr1iter.
simpl.
apply idpath.
-
apply funextfun; intro x.
simpl in x.
destruct x.
unfold compose.
simpl.
unfold pr1iter.
simpl.
unfold auxInd.

cbn.
apply idpath.
cbn.
simpl in x.
simpl.
Search (CoproductIn1 _ ;; _ = CoproductIn1 _ ;; _).
cbn.
unfold compose.
simpl.

Lemma rec : forall (l : pr1 List), P l.
Proof.
intro l.
set (pr2 (auxInd l)).
simpl in y.
unfold auxInd in y.
assert (test : (pr1 (iter P'HSET P0' Pc' l) = l)).
Check ((iter P'HSET P0' Pc' l)).
unfold iter, iter_map, bd, ad.
simpl.
simpl.
simpl.
simpl.

simpl in y.
intros l.
assert (

End ind.



Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Definition natHSET : HSET.
Proof.
exists nat.
abstract (apply isasetnat).
Defined.

Definition length : HSET⟦List,natHSET⟧.
Proof.
apply iter_map.
simpl.
apply 0.
simpl.
intros x.
apply (S (pr2 x)).
Defined.

(* Get induction as well? *)

End lists.

Definition nilnat : pr1 (List natHSET).
Proof.
apply nil.
Defined.

Definition testlist : pr1 (List natHSET).
Proof.
apply cons.
split.
apply 5.
apply cons.
split.
apply 2.
apply nil.
Defined.

Eval compute in length _ nilnat.
Eval compute in length _ testlist.

Definition test : UU.
apply (list natHSET).
set (f := nil natHSET).
simpl in f.
generalize (f tt).
intro A.
simple refine (tpair _ _ _).
apply A.
unfold category_hset_structures.cobase.
simpl.
admit.
simpl.
admit.
Admitted.