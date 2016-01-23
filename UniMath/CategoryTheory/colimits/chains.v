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

Context {C D : precategory}. (* (hsC : has_homsets C). *)

(* Define the chain:

     0 --> 1 --> 2 --> 3 --> ...

   with exactly one arrow from n to S n.
*)
Definition nat_graph : graph :=
  tpair (λ D : UU, D → D → UU) nat (λ m n, S m = n).

Local Notation "'chain'" := (diagram nat_graph).

Definition mapchain (F : functor C D) (c : chain C) : chain D.
Proof.
simple refine (tpair _ _ _).
- intros n.
  apply (F (dob c n)).
- simpl; intros m n e.
  apply (# F (dmor c e)).
Defined.

Definition mapcocone (F : functor C D) {c : chain C} {x : C} (cx : cocone c x) :
  cocone (mapchain F c) (F x).
Proof.
simple refine (mk_cocone _ _).
- simpl; intro n.
  exact (#F (coconeIn cx n)).
- abstract (intros u v e; destruct e ; simpl;
            rewrite <- functor_comp;
            apply maponpaths, (coconeInCommutes cx _ _ (idpath _ ))).
Defined.

Lemma mapcocone_chain_coconeIn (F : functor C D) {c : chain C} {x : C} (cx : cocone c x) (n : nat) :
  coconeIn (mapcocone F cx) n = #F (coconeIn cx n).
Proof.
  apply idpath.
Qed.

End chains.

Notation "'chain'" := (diagram nat_graph).

Definition omega_cocont {C D : precategory} (F : functor C D) : UU :=
  forall (c : chain C) (L : C) (cc : cocone c L),
  isColimCocone c L cc -> isColimCocone (mapchain F c) (F L) (mapcocone F cc).

(* Construct the chain:

         !          F!            F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Definition initChain {C : precategory} (Init : Initial C) (F : functor C C) : chain C.
Proof.
exists (λ n, iter_functor F n Init); simpl; intros m n Hmn.
destruct Hmn; simpl.
induction m; simpl.
- exact (InitialArrow Init _).
- exact (# F IHm).
Defined.

(* Proves that (L,m : F L -> L) is the initial algebra where L is the
   colimit of the inital chain:

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
(* Let a : cocone Fchain L := colimCocone CC. *)

Let FFchain : chain C := mapchain F Fchain.

Let Fa : cocone FFchain (F L) := mapcocone F (colimCocone CC).
Let FHC' : isColimCocone FFchain (F L) Fa :=
  HF Fchain L (colimCocone CC) (isColimCocone_from_ColimCocone CC).
Let FHC : ColimCocone FFchain := mk_ColimCocone _ _ _ FHC'.

Definition shiftCocone : cocone FFchain L.
Proof.
simple refine (mk_cocone _ _).
- simpl; intro n.
  apply (coconeIn (colimCocone CC) (S n)).
- simpl; intros m n e; destruct e.
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
    * apply colimArrow.
      apply (unshiftCocone _ cc).
    * simpl; intro n.
      apply (colimArrowCommutes CC x (unshiftCocone x cc) (S n)).
  + simpl. intros p.
    apply subtypeEquality.
    * intro f; apply impred; intro; apply hsC.
    * apply colimArrowUnique; simpl; intro n.
      destruct n as [|n]; [ apply InitialArrowUnique | apply (pr2 p) ].
Defined.

Definition shiftColimCocone : ColimCocone FFchain.
Proof.
simple refine (mk_ColimCocone _ _ _ _).
- apply L.
- apply shiftCocone.
- apply shiftIsColimCocone.
Defined.

Definition α_mor : C⟦F L,L⟧ := colimArrow FHC L shiftCocone.

Lemma is_iso_α_mor : is_iso α_mor.
Proof.
apply (isColim_is_iso _ FHC).
apply shiftIsColimCocone.
Defined.

Let α : iso (F L) L := isopair _ is_iso_α_mor.
Let α_inv : iso L (F L) := iso_inv_from_iso α.
Let α_alg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L α.

Section algebra.

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
Local Definition ad : C⟦L,A⟧.
Proof.
apply colimArrow.
simple refine (mk_cocone _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma adaggerCommutes (n : nat) : colimIn CC n ;; ad = an n.
Proof.
now apply colimArrowCommutes.
Qed.

Lemma ad_is_algebra_mor : is_algebra_mor _ α_alg Aa ad.
Proof.
unfold is_algebra_mor.
apply pathsinv0.
apply iso_inv_to_left.
apply colimArrowUnique; simpl; intro n.
induction n as [|n IHn].
- now apply InitialArrowUnique.
-
rewrite assoc.
 eapply pathscomp0.
  eapply cancel_postcomposition.
assert (H : inv_from_iso α = colimArrow
                                  (mk_ColimCocone FFchain L shiftCocone
                                     shiftIsColimCocone)
                                  (colim FHC) (colimCocone FHC)).
cbn.
unfold precomp_with.
apply id_right.
rewrite H.
apply (colimArrowCommutes  (mk_ColimCocone FFchain L shiftCocone
                            shiftIsColimCocone)).

  rewrite assoc.
unfold FHC.
simpl.
rewrite <- functor_comp.

apply cancel_postcomposition, maponpaths.
apply adaggerCommutes.
Qed.

Definition adaggerMor : algebra_mor F α_alg Aa := tpair _ _ ad_is_algebra_mor.

End algebra.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) α_alg.
Proof.
simple refine (mk_isInitial _ _ ).
intros Aa.
exists (adaggerMor Aa); simpl; intro Fa'.
apply (algebra_mor_eq _ hsC); simpl.
unfold ad.
apply colimArrowUnique; simpl; intro n.
destruct Fa' as [f hf]; simpl.
unfold is_algebra_mor in hf.
simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  apply cancel_postcomposition.
apply pathsinv0.
apply (iso_inv_to_right _ _ _ _ _ α).
assert (H : inv_from_iso α = colimArrow
                                  (mk_ColimCocone FFchain L shiftCocone
                                     shiftIsColimCocone)
                                  (colim FHC) (colimCocone FHC)).
cbn.
unfold precomp_with.
apply id_right.
rewrite H.
apply pathsinv0.
eapply pathscomp0.
apply (colimArrowCommutes (mk_ColimCocone FFchain L shiftCocone
                            shiftIsColimCocone)).
simpl.
apply idpath.
Qed.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  mk_Initial _ colimAlgIsInitial.

End colim_initial_algebra.

(* Section polynomial_functors. *)

(* Require Import UniMath.SubstitutionSystems.FunctorsPointwiseProduct. *)
(* Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct. *)
(* Require Import UniMath.CategoryTheory.limits.products. *)
(* Require Import UniMath.CategoryTheory.limits.coproducts. *)
(* Require Import UniMath.CategoryTheory.limits.terminal. *)

(* Variables (C : precategory) (hsC : has_homsets C) (InitC : Initial C). *)
(* (* Variables (F : functor C C) (CC : ColimCocone (Fchain F InitC)). *) *)

(* (* "good" functors *) *)
(* Let good F := Σ (CC : ColimCocone (Fchain InitC F)), omega_cocontinuous hsC InitC F CC. *)

(* (* TODO: Prove that polynomial functors are good *) *)
(* (* good(F), good(G) |- good(F * G) *) *)
(* (* good(F), good(G) |- good(F + G) *) *)
(* (*                  |- good(constant_functor A) *) *)
(* (*                  |- good(identity_functor) *) *)

(* (* constant_functor *) *)
(* Section constant_functor. *)

(* Variable (x : C). *)

(* Let Fx : functor C C := constant_functor C C x. *)

(* (* Lemma cocone_constant_functor : cocone (Fchain InitC Fx) x. *) *)
(* (* Proof. *) *)
(* (* simple refine (mk_cocone _ _). *) *)
(* (* + simpl; intro n. *) *)
(* (*   induction n; [ apply (InitialArrow InitC) | apply (identity x) ]. *) *)
(* (* + intros m n e; destruct e; apply id_right. *) *)
(* (* Defined. *) *)

(* Lemma Colimcocone_constant_functor : ColimCocone (Fchain InitC Fx). *)
(* Proof. *)
(* apply (unshift_colim _ hsC). *)
(* simple refine (mk_ColimCocone _ x _ _). *)
(* + simple refine (mk_cocone _ _). *)
(*   - simpl; intro n; apply (identity x). *)
(*   - simpl; intros m n e; induction e; apply id_right. *)
(* + intros a cc; simpl. *)
(*   simple refine (tpair _ _ _). *)
(*   - apply (tpair _ (coconeIn cc 0)); intro n. *)
(*     rewrite id_left. *)
(*     destruct cc as [f Hf]; simpl. *)
(*     induction n; [apply idpath|]. *)
(*     now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left. *)
(*   - simpl; intro p. *)
(*     apply subtypeEquality. *)
(*     * intros f; apply impred; intro; apply hsC. *)
(*     * simpl; destruct p as [p H]; generalize (H 0); simpl. *)
(*       now rewrite id_left. *)
(* Defined. *)

(* Lemma goodConstantFunctor : good Fx. *)
(* Proof. *)
(* apply (tpair _ Colimcocone_constant_functor), isColim_is_iso. *)
(* intros a cc; simpl. *)
(* (* from here on the proof is identitical to the one above. refactor? *) *)
(* simple refine (tpair _ _ _). *)
(* - apply (tpair _ (coconeIn cc 0)); intro n. *)
(*   rewrite id_left. *)
(*   destruct cc as [f Hf]; simpl. *)
(*   induction n; [apply idpath|]. *)
(*   now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left. *)
(* - simpl; intro p. *)
(*   apply subtypeEquality. *)
(*   + intros f; apply impred; intro; apply hsC. *)
(*   + simpl; destruct p as [p H]; generalize (H 0); simpl. *)
(*     now rewrite id_left. *)
(* Defined. *)

(* End constant_functor. *)

(* Section identity_functor. *)

(* Let Fid : functor C C := functor_identity C. *)

(* (* Lemma cocone_functor_identity : cocone (Fchain InitC Fid) InitC. *) *)
(* (* Proof. *) *)
(* (* simple refine (mk_cocone _ _). *) *)
(* (* + simpl; intro n. *) *)
(* (*   induction n; [ apply (InitialArrow InitC)| apply IHn]. *) *)
(* (* + intros m n e; destruct e; induction m as [|m IH]; *) *)
(* (*     [apply InitialArrowUnique | apply IH]. *) *)
(* (* Defined. *) *)

(* Lemma iter_functor_id (x : C) ( n : nat) : iter_functor Fid n x = x. *)
(* Proof. *)
(* induction n as [|n IH]; [apply idpath|apply IH]. *)
(* Defined. *)

(* Lemma Colimcocone_functor_identity : ColimCocone (Fchain InitC Fid). *)
(* Proof. *)
(* simple refine (mk_ColimCocone _ InitC _ _). *)
(* + simple refine (mk_cocone _ _). *)
(*   - simpl; intro n. *)
(*     rewrite iter_functor_id. *)
(*     apply (identity InitC). *)
(*   - simpl; intros m n e; induction e; simpl. *)
(*     induction m. *)
(*     simpl. *)
(*     rewrite id_right; apply pathsinv0, InitialArrowUnique. *)
(*     simpl. *)
(*     apply IHm. *)
(* + intros a cc; simpl. *)
(*   simple refine (tpair _ _ _). *)
(*   - simple refine (tpair _ _ _); [ apply (InitialArrow InitC) |]. *)
(* intro n. *)
(* induction n. *)
(* * destruct cc. *)
(* rewrite id_left. *)
(* apply pathsinv0, InitialArrowUnique. *)
(* * simpl; rewrite IHn. *)
(* destruct cc. *)
(* simpl. *)
(* generalize (p n _ (idpath _)). *)
(* intros H. *)
(* rewrite <- H. *)
(* clear H. *)
(* apply remove_id_left; [|apply idpath]. *)
(* simpl. *)
(* clear IHn. *)
(* induction n. *)
(* apply pathsinv0, InitialArrowUnique. *)
(* simpl. *)
(* rewrite IHn. *)
(* apply idpath. *)
(* - intros x. *)
(*     apply subtypeEquality. *)
(*     * intros f; apply impred; intro; apply hsC. *)
(* * apply InitialArrowUnique. *)
(* Defined. *)

(* Lemma goodIdentityFunctor : good Fid. *)
(* Proof. *)
(* apply (tpair _ Colimcocone_functor_identity), isColim_is_iso. *)
(* intros a cc; simpl. *)
(* simple refine (tpair _ _ _). *)
(* - apply (tpair _ (coconeIn cc 0)); intro n. *)
(* induction n. *)
(* * destruct cc. *)
(* rewrite id_left. *)
(* apply idpath. *)
(* * simpl; rewrite IHn. *)
(* destruct cc. *)
(* simpl. *)
(* generalize (p n _ (idpath _)). *)
(* intros H. *)
(* rewrite <- H. *)
(* clear H. *)
(* apply remove_id_left; [|apply idpath]. *)
(* simpl. *)
(* clear IHn. *)
(* induction n. *)
(* apply pathsinv0, InitialArrowUnique. *)
(* simpl. *)
(* rewrite IHn. *)
(* apply idpath. *)
(* - *)
(* intros x. *)
(*     apply subtypeEquality. *)
(*     * intros f; apply impred; intro; apply hsC. *)
(* * apply InitialArrowEq. *)
(* Defined. *)

(* End identity_functor. *)

(* Section product_functor. *)

(* Variable (HP : Products C). *)
(* Variables (F G : functor C C). *)

(* Lemma iter_functor_product (x : C) (n : nat) : *)
(*   iter_functor (product_functor C C HP F G) (S n) x = *)
(*   ProductObject _ (HP (iter_functor F (S n) x) (iter_functor G (S n) x)). *)
(* Proof. *)
(* simpl. *)
(* induction n. *)
(* - simpl. *)
(* apply idpath. *)
(* - simpl. *)
(* (* rewrite IHn. *) *)

(* unfold product_functor_ob in *. *)

(* rewrite IHn. *)
(* set (W := (ProductObject C *)
(*               (HP (F ((iter_functor F n) x)) (G ((iter_functor G n) x))))). *)
(* set (W1 := (F ((iter_functor F n) x))). *)
(* set (W2 :=  (G ((iter_functor G n) x))). *)
(* rewrite IHn. *)
(* Search ProductObject. *)
(* admit. *)
(* Admitted. *)

(* Lemma colimCocone_product (ccF : ColimCocone (Fchain InitC F)) *)
(*                           (ccG : ColimCocone (Fchain InitC G)) : *)
(*         ColimCocone (Fchain InitC (product_functor _ _ HP F G)). *)
(* Proof. *)
(* simple refine (mk_ColimCocone _ _ _ _). *)
(* - apply (ProductObject _ (HP (colim ccF) (colim ccG))). *)
(* - *)
(* simple refine (mk_cocone _ _). *)
(* simpl; intro n. *)
(* destruct n. *)
(* simpl. *)
(* apply InitialArrow. *)
(* rewrite iter_functor_product. *)
(* (* set (Fn := pr1 (Fchain InitC F) n). _ (idpath _)). *) *)
(* (* set (Gn := pr2 (Fchain InitC G) n _ (idpath _)). *) *)
(* apply ProductOfArrows. *)
(* apply (colimIn ccF (S n)). *)
(* apply (colimIn ccG (S n)). *)
(* Admitted. *)


(* End product_functor. *)

(* End polynomial_functors. *)




(* unfold good, omega_cocontinuous. *)
(*   unfold from_colim_shift. *)
(*   set (X1 := ColimCoconeHSET _ _). *)
(*   set (X3 := Fcocone _ _ _ _). *)
(*   apply (isColim_is_iso _ X1). *)
(*   intros a ca. *)
(*   refine (tpair _ _ _). *)
(*   - refine (tpair _ _ _). *)
(*     + apply colimArrow. *)
(*       apply ca. *)
(*     + intro n; induction n. *)
(*       * unfold X3. *)
(*         unfold Fcocone. *)
(*         rewrite unshift_cocone_coconeIn_O. *)
(*         simpl. *)
(*         assert (T:= ArrowsFromInitial InitialHSET). *)
(*         match goal with [T : _ |- ?e = ?f ] => *)
(*                         assert (T':= T _ e f) end. *)
(*         apply T'. *)
(*       * unfold X3. *)
(*         rewrite Fcocone_coconeIn_S. *)
(*         simpl. *)
(*         assert (H:=colimArrowCommutes X1 a ca ). *)
(*         eapply pathscomp0. *)
(*         apply H. *)
(*         assert (T:= coconeInCommutes ca n (S n) (idpath _ )). *)
(*         simpl in T. *)
(*         (* NOW USE HYPOTHESIS T, EXCEPT THAT THERE IS AN IDENTITY *)
(*            MORPHISM *) *)
(*         match goal with [|- ?e = ?f ] => *)
(*                         set (E:=e); set (F:=f) end. *)
(*         simpl in E,F. *)
(*         (* now use lemma that says that *)
(*              iter_functor (Id) (a) = a *)
(*              here a is initial object *)
(*            then use lemma ArrowsFromInitial, that is, *)
(*            both E and F start in initial object, hence E = F *)
(*         *) *)


(*
Lemma goodConstant (B : HSET) : good (constant_functor _ _ B).
Admitted.
 *)
(*
Lemma goodProduct (F G : functor HSET HSET) :
  good F -> good G -> good (product_functor _ _ ProductsHSET F G).
Admitted.
*)
(*
Lemma goodCoproduct (F G : functor HSET HSET) :
  good F -> good G -> good (coproduct_functor _ _ CoproductsHSET F G).
Admitted.


End good_functors.

(* WIP below of here *)
Section lists.

(* TODO: Move *)

Variable A : HSET.

(* F(X) = A * X *)
Definition streamFunctor : functor HSET HSET :=
  product_functor HSET HSET ProductsHSET
                  (constant_functor HSET HSET A)
                  (functor_identity HSET).

(* F(X) = 1 + (A * X) *)

(*
Definition listFunctor : functor HSET HSET :=
  coproduct_functor HSET HSET CoproductsHSET
                    (constant_functor HSET HSET (TerminalObject TerminalHSET))
                    streamFunctor.
*)

(* Let ColimCoconeF F := ColimCocone *)
(*          (Fchain F (InitialObject InitialHSET) *)
(*             (InitialArrow InitialHSET (F (InitialObject InitialHSET)))). *)

(* Definition temp : ColimCoconeF listFunctor := ColimCoconeHSET _ _. *)

(*
Let good F := omega_cocontinuous has_homsets_HSET F
    (InitialObject InitialHSET) (InitialArrow InitialHSET _) (ColimCoconeHSET _ _).
*)
(* TODO: *)
(* good(F), good(G) |- good(F * G) *)
(* good(F), good(G) |- good(F + G) *)
(*                  |- good(constant_functor A) *)
(*                  |- good(identity_functor) *)
(*
Lemma goodIdentity : good (functor_identity _).
Proof.
(* unfold good, omega_cocontinuous. *)
(* unfold from_colim_shift. *)
(* set (X1 := ColimCoconeHSET _ _). *)
(* set (X3 := Fcocone _ _ _ _). *)
(* apply (isColim_is_iso _ X1). *)
(* intros a ca. *)
(* simple refine (tpair _ _ _). *)
(* simple refine (tpair _ _ _). *)
(* apply colimArrow. *)
(* apply ca. *)
(* intros v. *)
(* set (H:=colimArrowCommutes X1 a ca v). *)
(* unfold colimIn in H. *)
(* unfold X3. *)
(* rewrite <- H. *)
(* apply cancel_postcomposition. *)
(* assert (test : Fcocone (functor_identity HSET) (InitialObject InitialHSET) *)
(*         (InitialArrow InitialHSET *)
(*            ((functor_identity HSET) (InitialObject InitialHSET))) X1 = colimCocone X1). *)
(* simpl. *)
(* apply subtypeEquality. *)
(* intro x. *)
(* repeat (apply impred; intro). *)
(* apply has_homsets_HSET. *)
(* simpl. *)
(* apply funextsec; intro n. *)
(* induction n; simpl. *)
(* apply (ArrowsFromInitial InitialHSET). *)
(* simpl. *)
(* admit. *)
(* rewrite test. *)
(* apply idpath. *)

(* apply InitialArrowUnique. *)

(* intro a; simpl. *)
(* unfold Fcocone. *)
(* unfold colimCocone. *)


(* induction v. *)
(* simpl. *)
(* apply idpath. *)
(* f_equal. *)
(* apply H. *)
(* simpl. *)
(* simpl. *)
(* simpl in *. *)
Admitted.
 *)
(*
Lemma goodConstant (B : HSET) : good (constant_functor _ _ B).
Admitted.
 *)
(*
Lemma goodProduct (F G : functor HSET HSET) :
  good F -> good G -> good (product_functor _ _ ProductsHSET F G).
Admitted.
*)
(*
Lemma goodCoproduct (F G : functor HSET HSET) :
  good F -> good G -> good (coproduct_functor _ _ CoproductsHSET F G).
Admitted.


Lemma listFunctor_omega_cocontinuous : good listFunctor.
Proof.
unfold listFunctor, streamFunctor.
apply goodCoproduct; [ apply goodConstant |].
apply goodProduct; [ apply goodConstant | apply goodIdentity].
Defined.

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg listFunctor has_homsets_HSET).
Proof.
simple refine (colimAlgInitial _ _ _ _ _ _).
- apply InitialHSET.
- apply ColimCoconeHSET.
- apply listFunctor_omega_cocontinuous.
Defined.
 *)

(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       iter x f : List A -> X *)

(* Get induction as well? *)

End lists.
*)




(************************** OLD VERSION BELOW  *)

(*


Section move_upstream.

(* Move to limits.initial *)

Fixpoint iter_functor {C : precategory} (F : functor C C) (n : nat) : functor C C := match n with
  | O => functor_identity C
  | S n' => functor_composite _ _ _ (iter_functor F n') F
  end.

(* Proof. *)
(* induction n as [|n Fn]. *)
(*   now apply functor_identity. *)
(* now apply (functor_composite _ _ _ Fn F). *)
(* Defined. *)

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

Variables (C : precategory) (hsC : has_homsets C).

(* Define the chain:

     0 --> 1 --> 2 --> 3 --> ...

   with exactly one arrow from n to S n.
*)
Definition nat_graph : graph :=
  tpair (λ D : UU, D → D → UU) nat (λ m n, S m = n).

(* Alternative definition of chains: *)
(* Definition chain := Σ (f0 : nat -> C), ∀ n, C⟦f0 n,f0 (S n)⟧. *)

(* Definition to_chain : diagram nat_graph C -> chain. *)
(* Proof. *)
(* intro D. *)
(* exists (pr1 D); intro n. *)
(* now apply (pr2 D). *)
(* Defined. *)

(* Definition from_chain : chain -> diagram nat_graph C. *)
(* Proof. *)
(* intro c. *)
(* exists (pr1 c); simpl; intros m n Hmn. *)
(* destruct Hmn. *)
(* now apply (pr2 c). *)
(* Defined. (* Maybe define using idtoiso? *) *)

Local Notation "'chain'" := (diagram nat_graph).

(* Drop the first element of the diagram *)
Definition shift (d : chain C) : chain C.
Proof.
exists (λ n, pr1 d (S n)); simpl; intros m n Hmn.
destruct Hmn.
now apply (pr2 d).
Defined.

(* Construct a cocone over the shifted diagram *)
Definition shift_cocone {D : chain C}
  {x : C} (cx : cocone D x) : cocone (shift D) x.
Proof.
simple refine (tpair _ _ _).
- now intro n; apply (coconeIn cx).
- abstract (now intros m n Hmn; destruct Hmn; apply (coconeInCommutes cx)).
Defined.

Lemma shift_cocone_coconeIn (D : diagram nat_graph C) (x : C) (cx : cocone D x) (n : nat):
  coconeIn (shift_cocone cx) n = coconeIn cx (S n).
Proof.
  apply idpath.
Qed.

(* Construct a cocone over the non-shifted diagram *)
Definition unshift_cocone {D : chain C}
  {x : C} (cx : cocone (shift D) x) : cocone D x.
Proof.
simple refine (mk_cocone _ _).
- intro n.
  now apply (@dmor _ _ _ n _ (idpath _) ;; coconeIn cx n).
- abstract (now intros m n Hmn; destruct Hmn; simpl;
            apply maponpaths, (coconeInCommutes cx _ _ (idpath _))).
Defined.

Lemma unshift_cocone_coconeIn_S (D : diagram nat_graph C) (x : C) (cx : cocone (shift D) x) (n : nat):
  coconeIn (unshift_cocone cx) (S n) = coconeIn cx n.
Proof.
  simpl.
  apply (coconeInCommutes cx _ _ (idpath _ )).
Qed.

Lemma unshift_cocone_coconeIn_O (D : diagram nat_graph C) (x : C) (cx : cocone (shift D) x) :
  coconeIn (unshift_cocone cx) 0 = dmor D (idpath 1) ;; coconeIn cx 0.
Proof.
  apply idpath.
Qed.

Lemma unshift_shift_cocone (D : chain C)
  (x : C) (cx : cocone D x) : unshift_cocone (shift_cocone cx) = cx.
Proof.
apply subtypeEquality; simpl.
- intro. now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx).
Qed.

Lemma shift_unshift_cocone (D : chain C)
  (x : C) (cx : cocone (shift D) x) : shift_cocone (unshift_cocone cx) = cx.
Proof.
apply subtypeEquality; simpl.
- intro. now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx _ _ (idpath _)).
Qed.

(* Construct the colimit of the shifted diagram *)
Definition shift_colim (D : chain C) (CC : ColimCocone D) :
  ColimCocone (shift D).
Proof.
apply (mk_ColimCocone _ (colim CC) (shift_cocone (colimCocone CC))).
intros x fx.
simple refine (tpair _ _ _).
+ exists (colimArrow CC x (unshift_cocone fx)).
  abstract (intro n; simpl;
            eapply pathscomp0;
              [ apply (colimArrowCommutes _ _ (unshift_cocone _))
              | now apply (coconeInCommutes fx _ _ (idpath _)) ]).
+ abstract (simpl; intro f;
            apply subtypeEquality; simpl;
              [ intro; now apply impred; intro; apply hsC | ];
            apply colimArrowUnique; simpl; intro n;
            destruct f as [f Hf]; simpl;
            rewrite <- (Hf n), assoc;
            now apply cancel_postcomposition, pathsinv0, (@colimInCommutes C)).
Defined.

(* Construct the colimit of the unshifted diagram *)
Definition unshift_colim (D : chain C) (CC : ColimCocone (shift D)) :
  ColimCocone D.
Proof.
apply (mk_ColimCocone _ (colim CC) (unshift_cocone (colimCocone CC))).
intros x fx.
simple refine (tpair _ _ _).
+ exists (colimArrow CC x (shift_cocone fx)).
  abstract (simpl; intro n;
            rewrite <- assoc;
            eapply pathscomp0;
              [ apply maponpaths, (colimArrowCommutes CC x _ n)
              | simpl; now eapply pathscomp0;
                  [|apply (coconeInCommutes fx _ _ (idpath _))]]).
+ abstract (simpl; intro f;
            apply subtypeEquality;
              [ intro; now apply impred; intro; apply hsC|]; simpl;
            apply colimArrowUnique; simpl; intro n;
            destruct f as [f Hf]; simpl;
            rewrite <- Hf;
            apply cancel_postcomposition, pathsinv0;
            now apply (colimInCommutes CC _ _ (idpath _))).
Defined.

Definition colim_shift_iso (D : chain C)
 (CC : ColimCocone D) : iso (colim CC) (colim (shift_colim D CC)).
Proof.
now apply identity_iso.
Defined.

End chains.

Notation "'chain'" := (diagram nat_graph).

Section functor_chain.

Context {C : precategory} (hsC : has_homsets C) (Init : Initial C).
Context (F : functor C C).

(* Construct the chain:

         !          F!            F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Definition Fchain : chain C.
Proof.
exists (λ n, iter_functor F n (InitialObject Init)); simpl; intros m n Hmn.
destruct Hmn; simpl.
induction m; simpl.
- exact (InitialArrow Init _).
- exact (# F IHm).
Defined.

(* More general version: *)
(* Context (c : C) (s : C⟦c,F c⟧). *)

(* Construct the chain:

         s          Fs            F^2 s
     c -----> F c ------> F^2 c --------> F^3 c ---> ...

*)
(* Definition Fchain : chain C. *)
(* Proof. *)
(* exists (λ n, iter_functor F n c); simpl; intros m n Hmn. *)
(* destruct Hmn; simpl. *)
(* induction m; simpl. *)
(* - exact s. *)
(* - exact (# F IHm). *)
(* Defined. *)

(** Experiment with map and Fchain *)
Definition functormap_Fchain (x : C) : cocone Fchain x -> cocone (shift C Fchain) (F x).
Proof.
  intro cx.
  simple refine (mk_cocone _ _).
  - simpl.
    intro n.
    exact (#F (coconeIn cx n)).
  - abstract (intros u v e;
               destruct e ; simpl;
               rewrite <- functor_comp;
               apply maponpaths;
               apply (coconeInCommutes cx _ _ (idpath _ ))).
(*
    destruct n.
    + exact (# F (coconeIn H 0)).
    + exact (# F (coconeIn H (S n))).

  - simpl; intros m n e; destruct e.
    destruct m; simpl.
    + rewrite <- functor_comp.
      apply maponpaths, (pr2 H 0 1 (idpath _)). (* remove pr2 ... *)
    + rewrite <- functor_comp.
      apply maponpaths, (pr2 H (S m) (S (S m)) (idpath _)). (* remove pr2 *)
*)
Defined.

Lemma functormap_Fchain_coconeIn (x : C) (cx : cocone Fchain x) (n : nat) :
  coconeIn (functormap_Fchain x cx) n = #F (coconeIn cx n).
Proof.
  apply idpath.
Qed.

Definition Fcocone {x : C} (cx : cocone Fchain x) : cocone Fchain (F x).
Proof.
  apply unshift_cocone.
  apply functormap_Fchain.
  apply cx.
Defined.

Lemma Fcocone_coconeIn_S (x : C) (cx : cocone Fchain x) n :
  coconeIn (Fcocone cx) (S n) = #F (coconeIn cx n ).
Proof.
  unfold Fcocone.
  rewrite unshift_cocone_coconeIn_S.
  apply functormap_Fchain_coconeIn.
Qed.
(*
Lemma Fcocone_coconeIn_O (x : C) (cx : cocone Fchain x) :
  coconeIn (Fcocone cx) 0 = #F (dmor Fchain  (idpath _) ;; coconeIn cx _). #F (dmor Fchain (idpath _) ;;  (cocoeIn cx 1)).
Proof.
  unfold Fcocone.
  rewrite unshift_cocone_coconeIn_S.
  apply shift_Fchain_coconeIn.
Qed.
*)

Variables (CC : ColimCocone Fchain).

Local Notation L := (colim CC).
Local Notation LF := (colim (shift_colim C hsC Fchain CC)).

(* Definition Fcocone : cocone Fchain (F L). *)
(* Proof. *)
(* simple refine (mk_cocone _ _). *)
(* - intro n. *)
(*   destruct n; simpl. *)
(*   + exact (InitialArrow Init _ ;; # F (colimIn CC 0)). *)
(*   + exact (# F (colimIn CC n)). *)
(* - abstract (simpl; intros m n Hmn; destruct Hmn; simpl; destruct m; simpl; *)
(*             [apply idpath|]; simpl; rewrite <- functor_comp; apply maponpaths; *)
(*             apply (colimInCommutes CC _ _ (idpath _))). *)
(* Defined. *)

Definition functormap_colimCocone : cocone (shift C Fchain) (F L) :=
  functormap_Fchain L (colimCocone CC).

(* this is m^-1 : L -> FL in TACL slides page 9 *)
Definition from_colim_shift : C⟦LF,F L⟧ := colimArrow _ _ functormap_colimCocone. (* (Fcocone (colimCocone CC)). *)

(* This uses that LF and L are convertible *)
Definition from_colim : C⟦L,F L⟧ := from_colim_shift.

Definition omega_cocontinuous : UU := is_iso from_colim_shift.

(* This could also be defined as: *)
(* Definition omega_cocontinuous : UU := is_iso from_colim. *)

Variable Hcc : omega_cocontinuous.
Let minv : iso L (F L) := isopair _ Hcc.
Let m : C⟦F L,L⟧ := inv_from_iso minv.

Lemma mCommutes (n : nat) : coconeIn (colimCocone CC) n = coconeIn (Fcocone (colimCocone CC)) n ;; m.
Proof.
now apply iso_inv_on_left, pathsinv0, (colimArrowCommutes _ _ (Fcocone _)).
Qed.

Lemma minvCommutes (n : nat) : coconeIn (colimCocone CC) n ;; minv = coconeIn (Fcocone (colimCocone CC)) n.
Proof.
now apply (colimArrowCommutes _ _ (Fcocone _)).
Qed.

End functor_chain.

(* Proves that (L,m : F L -> L) is the initial algebra where L is the
   colimit of the inital chain:

         !          F !           F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Section colim_initial_algebra.

Variables (C : precategory) (F : functor C C).
Variables (hsC : has_homsets C) (Init : Initial C).

Definition initDiag : chain C := Fchain Init F.

Variable (CC : ColimCocone initDiag).
Variable (Fcont : omega_cocontinuous hsC Init F CC).

Local Notation L := (colim CC).
Local Notation minv := (isopair _ Fcont).

Local Definition m : C⟦F L,L⟧ := inv_from_iso minv.
Local Definition colimAlg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L m.

Section algebra.

Variable (Aa : algebra_ob F).

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

Definition cocone_over_alg (n : nat) : C ⟦ dob initDiag n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn ;; a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

(* This makes Coq not unfold dmor during simpl *)
Arguments dmor : simpl never.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor initDiag e ;; an Sn = an n.
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
Local Definition ad : C⟦L,A⟧.
Proof.
apply colimArrow.
simple refine (mk_cocone _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma adaggerCommutes (n : nat) : colimIn CC n ;; ad = an n.
Proof.
now apply colimArrowCommutes.
Qed.

Lemma adaggerCommutes2 (n : nat) : colimIn CC n ;; minv ;; # F ad ;; a = an n.
Proof.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- rewrite <- assoc.
  eapply pathscomp0;
    [ eapply cancel_postcomposition; apply (minvCommutes hsC Init F CC Fcont (S n))|].
  rewrite assoc, Fcocone_coconeIn_S; simpl; rewrite <- (functor_comp F).
  now apply cancel_postcomposition, maponpaths, adaggerCommutes.
Qed.

Lemma adaggerDef : ad = minv ;; #F ad ;; a.
Proof.
apply pathsinv0, colimArrowUnique; simpl; intro n.
rewrite !assoc.
now apply adaggerCommutes2.
Qed.

Lemma ad_is_algebra_mor : is_algebra_mor _ colimAlg Aa ad.
Proof.
unfold is_algebra_mor; simpl; unfold colimAlg.
apply iso_inv_on_right.
rewrite assoc.
now apply adaggerDef.
Qed.

Definition adaggerMor : algebra_mor F colimAlg Aa := tpair _ _ ad_is_algebra_mor.

End algebra.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) colimAlg.
Proof.
simple refine (mk_isInitial _ _ ).
intros Aa.
exists (adaggerMor Aa); simpl; intro Fa.
apply (algebra_mor_eq _ hsC); simpl.
unfold ad.
apply colimArrowUnique; simpl; intro n.
destruct Fa as [f hf]; simpl.
unfold is_algebra_mor in hf.
simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  apply cancel_postcomposition.
  assert (T:= mCommutes hsC Init _ CC Fcont (S n)).
  unfold colimIn.
  eapply pathscomp0. apply T.
  apply cancel_postcomposition.
  apply Fcocone_coconeIn_S.
Qed.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  mk_Initial _ colimAlgIsInitial.

End colim_initial_algebra.
Check colimAlgInitial.
Section polynomial_functors.

Require Import UniMath.SubstitutionSystems.FunctorsPointwiseProduct.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Variables (C : precategory) (hsC : has_homsets C) (InitC : Initial C).
(* Variables (F : functor C C) (CC : ColimCocone (Fchain F InitC)). *)

(* "good" functors *)
Let good F := Σ (CC : ColimCocone (Fchain InitC F)), omega_cocontinuous hsC InitC F CC.

(* TODO: Prove that polynomial functors are good *)
(* good(F), good(G) |- good(F * G) *)
(* good(F), good(G) |- good(F + G) *)
(*                  |- good(constant_functor A) *)
(*                  |- good(identity_functor) *)

(* constant_functor *)
Section constant_functor.

Variable (x : C).

Let Fx : functor C C := constant_functor C C x.

(* Lemma cocone_constant_functor : cocone (Fchain InitC Fx) x. *)
(* Proof. *)
(* simple refine (mk_cocone _ _). *)
(* + simpl; intro n. *)
(*   induction n; [ apply (InitialArrow InitC) | apply (identity x) ]. *)
(* + intros m n e; destruct e; apply id_right. *)
(* Defined. *)

Lemma Colimcocone_constant_functor : ColimCocone (Fchain InitC Fx).
Proof.
apply (unshift_colim _ hsC).
simple refine (mk_ColimCocone _ x _ _).
+ simple refine (mk_cocone _ _).
  - simpl; intro n; apply (identity x).
  - simpl; intros m n e; induction e; apply id_right.
+ intros a cc; simpl.
  simple refine (tpair _ _ _).
  - apply (tpair _ (coconeIn cc 0)); intro n.
    rewrite id_left.
    destruct cc as [f Hf]; simpl.
    induction n; [apply idpath|].
    now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left.
  - simpl; intro p.
    apply subtypeEquality.
    * intros f; apply impred; intro; apply hsC.
    * simpl; destruct p as [p H]; generalize (H 0); simpl.
      now rewrite id_left.
Defined.

Lemma goodConstantFunctor : good Fx.
Proof.
apply (tpair _ Colimcocone_constant_functor), isColim_is_iso.
intros a cc; simpl.
(* from here on the proof is identitical to the one above. refactor? *)
simple refine (tpair _ _ _).
- apply (tpair _ (coconeIn cc 0)); intro n.
  rewrite id_left.
  destruct cc as [f Hf]; simpl.
  induction n; [apply idpath|].
  now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left.
- simpl; intro p.
  apply subtypeEquality.
  + intros f; apply impred; intro; apply hsC.
  + simpl; destruct p as [p H]; generalize (H 0); simpl.
    now rewrite id_left.
Defined.

End constant_functor.

Section identity_functor.

Let Fid : functor C C := functor_identity C.

(* Lemma cocone_functor_identity : cocone (Fchain InitC Fid) InitC. *)
(* Proof. *)
(* simple refine (mk_cocone _ _). *)
(* + simpl; intro n. *)
(*   induction n; [ apply (InitialArrow InitC)| apply IHn]. *)
(* + intros m n e; destruct e; induction m as [|m IH]; *)
(*     [apply InitialArrowUnique | apply IH]. *)
(* Defined. *)

Lemma iter_functor_id (x : C) ( n : nat) : iter_functor Fid n x = x.
Proof.
induction n as [|n IH]; [apply idpath|apply IH].
Defined.

Lemma Colimcocone_functor_identity : ColimCocone (Fchain InitC Fid).
Proof.
simple refine (mk_ColimCocone _ InitC _ _).
+ simple refine (mk_cocone _ _).
  - simpl; intro n.
    rewrite iter_functor_id.
    apply (identity InitC).
  - simpl; intros m n e; induction e; simpl.
    induction m.
    simpl.
    rewrite id_right; apply pathsinv0, InitialArrowUnique.
    simpl.
    apply IHm.
+ intros a cc; simpl.
  simple refine (tpair _ _ _).
  - simple refine (tpair _ _ _); [ apply (InitialArrow InitC) |].
intro n.
induction n.
* destruct cc.
rewrite id_left.
apply pathsinv0, InitialArrowUnique.
* simpl; rewrite IHn.
destruct cc.
simpl.
generalize (p n _ (idpath _)).
intros H.
rewrite <- H.
clear H.
apply remove_id_left; [|apply idpath].
simpl.
clear IHn.
induction n.
apply pathsinv0, InitialArrowUnique.
simpl.
rewrite IHn.
apply idpath.
- intros x.
    apply subtypeEquality.
    * intros f; apply impred; intro; apply hsC.
* apply InitialArrowUnique.
Defined.

Lemma goodIdentityFunctor : good Fid.
Proof.
apply (tpair _ Colimcocone_functor_identity), isColim_is_iso.
intros a cc; simpl.
simple refine (tpair _ _ _).
- apply (tpair _ (coconeIn cc 0)); intro n.
induction n.
* destruct cc.
rewrite id_left.
apply idpath.
* simpl; rewrite IHn.
destruct cc.
simpl.
generalize (p n _ (idpath _)).
intros H.
rewrite <- H.
clear H.
apply remove_id_left; [|apply idpath].
simpl.
clear IHn.
induction n.
apply pathsinv0, InitialArrowUnique.
simpl.
rewrite IHn.
apply idpath.
-
intros x.
    apply subtypeEquality.
    * intros f; apply impred; intro; apply hsC.
* apply InitialArrowEq.
Defined.

End identity_functor.

Section product_functor.

Variable (HP : Products C).
Variables (F G : functor C C).

Lemma iter_functor_product (x : C) (n : nat) :
  iter_functor (product_functor C C HP F G) (S n) x =
  ProductObject _ (HP (iter_functor F (S n) x) (iter_functor G (S n) x)).
Proof.
simpl.
induction n.
- simpl.
apply idpath.
- simpl.
(* rewrite IHn. *)

unfold product_functor_ob in *.

rewrite IHn.
set (W := (ProductObject C
              (HP (F ((iter_functor F n) x)) (G ((iter_functor G n) x))))).
set (W1 := (F ((iter_functor F n) x))).
set (W2 :=  (G ((iter_functor G n) x))).
rewrite IHn.
Search ProductObject.
admit.
Admitted.

Lemma colimCocone_product (ccF : ColimCocone (Fchain InitC F))
                          (ccG : ColimCocone (Fchain InitC G)) :
        ColimCocone (Fchain InitC (product_functor _ _ HP F G)).
Proof.
simple refine (mk_ColimCocone _ _ _ _).
- apply (ProductObject _ (HP (colim ccF) (colim ccG))).
-
simple refine (mk_cocone _ _).
simpl; intro n.
destruct n.
simpl.
apply InitialArrow.
rewrite iter_functor_product.
(* set (Fn := pr1 (Fchain InitC F) n). _ (idpath _)). *)
(* set (Gn := pr2 (Fchain InitC G) n _ (idpath _)). *)
apply ProductOfArrows.
apply (colimIn ccF (S n)).
apply (colimIn ccG (S n)).
Admitted.


End product_functor.

End polynomial_functors.




(* unfold good, omega_cocontinuous. *)
(*   unfold from_colim_shift. *)
(*   set (X1 := ColimCoconeHSET _ _). *)
(*   set (X3 := Fcocone _ _ _ _). *)
(*   apply (isColim_is_iso _ X1). *)
(*   intros a ca. *)
(*   refine (tpair _ _ _). *)
(*   - refine (tpair _ _ _). *)
(*     + apply colimArrow. *)
(*       apply ca. *)
(*     + intro n; induction n. *)
(*       * unfold X3. *)
(*         unfold Fcocone. *)
(*         rewrite unshift_cocone_coconeIn_O. *)
(*         simpl. *)
(*         assert (T:= ArrowsFromInitial InitialHSET). *)
(*         match goal with [T : _ |- ?e = ?f ] => *)
(*                         assert (T':= T _ e f) end. *)
(*         apply T'. *)
(*       * unfold X3. *)
(*         rewrite Fcocone_coconeIn_S. *)
(*         simpl. *)
(*         assert (H:=colimArrowCommutes X1 a ca ). *)
(*         eapply pathscomp0. *)
(*         apply H. *)
(*         assert (T:= coconeInCommutes ca n (S n) (idpath _ )). *)
(*         simpl in T. *)
(*         (* NOW USE HYPOTHESIS T, EXCEPT THAT THERE IS AN IDENTITY *)
(*            MORPHISM *) *)
(*         match goal with [|- ?e = ?f ] => *)
(*                         set (E:=e); set (F:=f) end. *)
(*         simpl in E,F. *)
(*         (* now use lemma that says that *)
(*              iter_functor (Id) (a) = a *)
(*              here a is initial object *)
(*            then use lemma ArrowsFromInitial, that is, *)
(*            both E and F start in initial object, hence E = F *)
(*         *) *)


(*
Lemma goodConstant (B : HSET) : good (constant_functor _ _ B).
Admitted.
 *)
(*
Lemma goodProduct (F G : functor HSET HSET) :
  good F -> good G -> good (product_functor _ _ ProductsHSET F G).
Admitted.
*)
(*
Lemma goodCoproduct (F G : functor HSET HSET) :
  good F -> good G -> good (coproduct_functor _ _ CoproductsHSET F G).
Admitted.


End good_functors.

(* WIP below of here *)
Section lists.

(* TODO: Move *)

Variable A : HSET.

(* F(X) = A * X *)
Definition streamFunctor : functor HSET HSET :=
  product_functor HSET HSET ProductsHSET
                  (constant_functor HSET HSET A)
                  (functor_identity HSET).

(* F(X) = 1 + (A * X) *)

(*
Definition listFunctor : functor HSET HSET :=
  coproduct_functor HSET HSET CoproductsHSET
                    (constant_functor HSET HSET (TerminalObject TerminalHSET))
                    streamFunctor.
*)

(* Let ColimCoconeF F := ColimCocone *)
(*          (Fchain F (InitialObject InitialHSET) *)
(*             (InitialArrow InitialHSET (F (InitialObject InitialHSET)))). *)

(* Definition temp : ColimCoconeF listFunctor := ColimCoconeHSET _ _. *)

(*
Let good F := omega_cocontinuous has_homsets_HSET F
    (InitialObject InitialHSET) (InitialArrow InitialHSET _) (ColimCoconeHSET _ _).
*)
(* TODO: *)
(* good(F), good(G) |- good(F * G) *)
(* good(F), good(G) |- good(F + G) *)
(*                  |- good(constant_functor A) *)
(*                  |- good(identity_functor) *)
(*
Lemma goodIdentity : good (functor_identity _).
Proof.
(* unfold good, omega_cocontinuous. *)
(* unfold from_colim_shift. *)
(* set (X1 := ColimCoconeHSET _ _). *)
(* set (X3 := Fcocone _ _ _ _). *)
(* apply (isColim_is_iso _ X1). *)
(* intros a ca. *)
(* simple refine (tpair _ _ _). *)
(* simple refine (tpair _ _ _). *)
(* apply colimArrow. *)
(* apply ca. *)
(* intros v. *)
(* set (H:=colimArrowCommutes X1 a ca v). *)
(* unfold colimIn in H. *)
(* unfold X3. *)
(* rewrite <- H. *)
(* apply cancel_postcomposition. *)
(* assert (test : Fcocone (functor_identity HSET) (InitialObject InitialHSET) *)
(*         (InitialArrow InitialHSET *)
(*            ((functor_identity HSET) (InitialObject InitialHSET))) X1 = colimCocone X1). *)
(* simpl. *)
(* apply subtypeEquality. *)
(* intro x. *)
(* repeat (apply impred; intro). *)
(* apply has_homsets_HSET. *)
(* simpl. *)
(* apply funextsec; intro n. *)
(* induction n; simpl. *)
(* apply (ArrowsFromInitial InitialHSET). *)
(* simpl. *)
(* admit. *)
(* rewrite test. *)
(* apply idpath. *)

(* apply InitialArrowUnique. *)

(* intro a; simpl. *)
(* unfold Fcocone. *)
(* unfold colimCocone. *)


(* induction v. *)
(* simpl. *)
(* apply idpath. *)
(* f_equal. *)
(* apply H. *)
(* simpl. *)
(* simpl. *)
(* simpl in *. *)
Admitted.
 *)
(*
Lemma goodConstant (B : HSET) : good (constant_functor _ _ B).
Admitted.
 *)
(*
Lemma goodProduct (F G : functor HSET HSET) :
  good F -> good G -> good (product_functor _ _ ProductsHSET F G).
Admitted.
*)
(*
Lemma goodCoproduct (F G : functor HSET HSET) :
  good F -> good G -> good (coproduct_functor _ _ CoproductsHSET F G).
Admitted.


Lemma listFunctor_omega_cocontinuous : good listFunctor.
Proof.
unfold listFunctor, streamFunctor.
apply goodCoproduct; [ apply goodConstant |].
apply goodProduct; [ apply goodConstant | apply goodIdentity].
Defined.

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg listFunctor has_homsets_HSET).
Proof.
simple refine (colimAlgInitial _ _ _ _ _ _).
- apply InitialHSET.
- apply ColimCoconeHSET.
- apply listFunctor_omega_cocontinuous.
Defined.
 *)

(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       iter x f : List A -> X *)

(* Get induction as well? *)

End lists.
*)

*)