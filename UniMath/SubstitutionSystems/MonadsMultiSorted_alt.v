(**

    Monads in [sort,C]

Written by Anders Mörtberg, 2021 (adapted from MonadsMultiSorted.v)

*)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Local Open Scope cat.

Section MonadInSortToC.

Variables (sort : hSet) (C : category) (BC : BinCoproducts C).

Let sortToC : category := [path_pregroupoid sort,C].
Let hs : has_homsets sortToC := homset_property sortToC.

Local Lemma BinCoproductsSortToC : BinCoproducts sortToC.
Proof.
apply BinCoproducts_functor_precat, BC.
Defined.

Local Notation "a ⊕ b" := (BinCoproductObject _ (BinCoproductsSortToC a b)).

Context {M : Monad sortToC}.

Definition sortToC_fun {X Y : sortToC} (f : ∏ t, C⟦pr1 X t,pr1 Y t⟧) : sortToC⟦X,Y⟧ :=
  nat_trans_functor_path_pregroupoid (homset_property _) f.

Definition bind_fun {X Y : sortToC} (f : ∏ t, C⟦pr1 X t,pr1 (M Y) t⟧) :
  ∏ t, C⟦pr1 (M X) t,pr1 (M Y) t⟧ :=
    λ t, pr1 (bind (sortToC_fun f)) t.

Definition η_fun {X : sortToC} (t : sort) : C⟦pr1 X t,pr1 (M X) t⟧ :=
  pr1 (η M X) t.

Lemma η_bind_fun {X Y : sortToC} (f : ∏ t, C⟦pr1 X t,pr1 (M Y) t⟧) (t : sort) :
  η_fun t · bind_fun f t = f t.
Proof.
exact (nat_trans_eq_pointwise (η_bind (sortToC_fun f)) t).
Qed.

Lemma bind_η_fun {X : sortToC} (t : sort) :
  bind_fun η_fun t = pr1 (identity (M X)) t.
Proof.
etrans; [|apply (nat_trans_eq_pointwise (@bind_η _ M X) t)].
apply cancel_postcomposition.
assert (H : sortToC_fun η_fun = η M X).
{ now apply nat_trans_eq; [apply homset_property|]. }
exact (nat_trans_eq_pointwise (maponpaths (λ a, # M a) H) t).
Qed.

Lemma bind_bind_fun {X Y Z : sortToC}
                    (f : ∏ t, C⟦pr1 X t,pr1 (M Y) t⟧)
                    (g : ∏ t, C⟦pr1 Y t, pr1 (M Z) t ⟧)
                    (t : sort) :
  bind_fun f t · bind_fun g t = bind_fun (λ s, f s · bind_fun g s) t.
Proof.
  etrans.
  apply (nat_trans_eq_pointwise (bind_bind (sortToC_fun f) (sortToC_fun g)) t).
  apply cancel_postcomposition.
  assert (H : sortToC_fun f · bind (sortToC_fun g) = sortToC_fun (λ s, f s · bind_fun g s)).
  { now apply nat_trans_eq; [apply homset_property|]. }
  exact (nat_trans_eq_pointwise (maponpaths (λ a, # M a) H) t).
Qed.


(** now we only substitute a single sorted variable *)



(* Definition aux_inject_N {Γ:SET_over_sort}(N : wellsorted_in Γ): *)
(*   SET_over_sort⟦constHSET_slice (sort_in N),T Γ⟧. *)
(* Proof. *)
(*   use tpair. *)
(*   + exact (fun _=> N). *)
(*   + now apply funextsec. *)
(* Defined. *)

Definition monadSubstGen_instantiated {X Y : sortToC} :
  sortToC⟦X,M Y⟧ → sortToC⟦M (X ⊕ Y),M Y⟧ := monadSubstGen M BinCoproductsSortToC Y.


Definition monadSubstGen_instantiated_fun {X Y : sortToC}
           (e : ∏ s, C⟦pr1 X s,pr1 (M Y) s⟧) (t : sort) : C⟦pr1 (M (X ⊕ Y)) t, pr1 (M Y) t⟧ :=
  pr1 (monadSubstGen_instantiated (sortToC_fun e)) t.


(*

Definition subst_slice {Γ:SET_over_sort}(N : wellsorted_in Γ)
  (M : wellsorted_in (sorted_option_functor (sort_in N) Γ)): wellsorted_in Γ :=
  pr1 (monadSubstGen_instantiated _ (aux_inject_N N)) M.

Lemma subst_slice_ok {Γ:SET_over_sort}(N : wellsorted_in Γ)
   (M : wellsorted_in (sorted_option_functor (sort_in N) Γ)): sort_in (subst_slice N M) = sort_in M.
Proof.
  assert (H1 := pr2 (monadSubstGen_instantiated _ (aux_inject_N N))).
  apply toforallpaths in H1.
  apply pathsinv0.
  now rewrite H1.
Qed.




Local Definition mweak_instantiated (Γ1 : SET_over_sort){Γ2 : SET_over_sort} :
  SET_over_sort⟦T Γ2,T (Γ1 ⊕ Γ2)⟧ := mweak T BC _ _.

Definition mweak_slice (Γ1 : SET_over_sort)(Γ2 : SET_over_sort) : wellsorted_in Γ2 -> wellsorted_in (Γ1 ⊕ Γ2) := pr1 (mweak_instantiated Γ1).

Arguments mweak_slice _ _ _ : clear implicits.

Lemma mweak_slice_ok (Γ1 : SET_over_sort){Γ2 : SET_over_sort}(M : wellsorted_in Γ2) :
  sort_in (mweak_slice Γ1 Γ2 M) = sort_in M.
Proof.
  set (H1 := pr2 (mweak_instantiated(Γ2:=Γ2) Γ1)).
  apply toforallpaths in H1.
  apply pathsinv0.
  now rewrite H1.
Qed.

Definition mweak_slice_as_bind_slice (Γ1 : SET_over_sort)(Γ2 : SET_over_sort)(M : wellsorted_in Γ2) : wellsorted_in (Γ1 ⊕ Γ2).
Proof.
  use (bind_slice (λ a1, η_slice(Γ:=Γ1 ⊕ Γ2) (pr1 (BinCoproductIn2 _ (BC _ _)) a1)) _ M).
  intro a1.
  simpl; now rewrite η_slice_ok.
Defined.

Lemma mweak_slice_as_bind_slice_agrees (Γ1 : SET_over_sort){Γ2 : SET_over_sort}(M : wellsorted_in Γ2) :
  mweak_slice_as_bind_slice Γ1 Γ2 M = mweak_slice Γ1 Γ2 M.
Proof.
  unfold mweak_slice_as_bind_slice, mweak_slice.
  unfold bind_slice, mweak_instantiated.
  apply (maponpaths (λ f, f M)).
  apply maponpaths.
  unfold mweak, bind_instantiated.
  apply maponpaths.
  now apply eq_mor_slicecat.
Qed.

Lemma mweak_slice_as_bind_slice_ok (Γ1 : SET_over_sort){Γ2 : SET_over_sort}(M : wellsorted_in Γ2) :
  sort_in (mweak_slice_as_bind_slice Γ1 Γ2 M) = sort_in M.
Proof.
  rewrite mweak_slice_as_bind_slice_agrees; apply mweak_slice_ok.
Qed.


Local Definition mexch_instantiated {Γ1 Γ2 Γ3: SET_over_sort} :
  SET_over_sort⟦T (Γ1 ⊕ (Γ2 ⊕ Γ3)), T (Γ2 ⊕ (Γ1 ⊕ Γ3))⟧ := mexch T BC _ _ _.

Definition mexch_slice {Γ1 Γ2 Γ3: SET_over_sort} :
  wellsorted_in (Γ1 ⊕ (Γ2 ⊕ Γ3)) -> wellsorted_in (Γ2 ⊕ (Γ1 ⊕ Γ3)) :=
  pr1 (mexch_instantiated).

Lemma mexch_slice_ok {Γ1 Γ2 Γ3: SET_over_sort}(M : wellsorted_in (Γ1 ⊕ (Γ2 ⊕ Γ3))) :
  sort_in (mexch_slice M) = sort_in M.
Proof.
  set (H1 := pr2 (mexch_instantiated(Γ1:=Γ1)(Γ2:=Γ2)(Γ3:=Γ3))).
  apply toforallpaths in H1.
  apply pathsinv0.
  now rewrite H1.
Qed.


Definition mexch_slice_as_bind_slice {Γ1 Γ2 Γ3: SET_over_sort}(M : wellsorted_in (Γ1 ⊕ (Γ2 ⊕ Γ3))) :
  wellsorted_in (Γ2 ⊕ (Γ1 ⊕ Γ3)).
Proof.
  (* first important preparations *)
  unfold BinCoproductObject in M.
  simpl in M.
  set (a1 := BinCoproductIn1 _ (BinCoproductsHSET _ _) · BinCoproductIn2 _ (BinCoproductsHSET _ _): HSET⟦pr1 Γ1, pr1(Γ2 ⊕ (Γ1 ⊕ Γ3))⟧).
  set (a21 := BinCoproductIn1 _ (BinCoproductsHSET _ _): HSET⟦pr1 Γ2, pr1(Γ2 ⊕ (Γ1 ⊕ Γ3))⟧).
  set (a22 := BinCoproductIn2 _ (BinCoproductsHSET _ _) · BinCoproductIn2 _ (BinCoproductsHSET _ _): HSET⟦pr1 Γ3, pr1(Γ2 ⊕ (Γ1 ⊕ Γ3))⟧).
  use (bind_slice ((BinCoproductArrow _ _ a1 (BinCoproductArrow _ _ a21 a22)) · η_slice(Γ:=Γ2 ⊕ (Γ1 ⊕ Γ3))) _ M).
  intro x.
  induction x as [x1 | x2].
  + unfold BinCoproductArrow.
    simpl.
    unfold compose.
    simpl.
    now rewrite η_slice_ok.
  + induction x2 as [x21 | x22].
    * unfold BinCoproductArrow.
      simpl.
      unfold compose.
      simpl.
      now rewrite η_slice_ok.
    * unfold BinCoproductArrow.
      simpl.
      unfold compose.
      simpl.
      now rewrite η_slice_ok.
Defined.

Lemma mexch_slice_as_bind_slice_agrees {Γ1 Γ2 Γ3: SET_over_sort}(M : wellsorted_in (Γ1 ⊕ (Γ2 ⊕ Γ3))) :
  mexch_slice_as_bind_slice M = mexch_slice M.
Proof.
  unfold mexch_slice_as_bind_slice, mexch_slice.
  unfold bind_slice, mexch_instantiated.
  apply (maponpaths (λ f, f M)).
  apply maponpaths.
  unfold mexch, bind_instantiated.
  apply maponpaths.
  now apply eq_mor_slicecat.
Qed.


Lemma mexch_slice_as_bind_slice_ok {Γ1 Γ2 Γ3: SET_over_sort}
      (M : wellsorted_in (Γ1 ⊕ (Γ2 ⊕ Γ3))) :
  sort_in (mexch_slice_as_bind_slice M) = sort_in M.
Proof.
  rewrite mexch_slice_as_bind_slice_agrees; apply mexch_slice_ok.
Qed.

Lemma subst_interchange_law_instantiated {t s:sort}{Γ: SET_over_sort}
      (NN:SET_over_sort⟦constHSET_slice t, T (constHSET_slice s ⊕ Γ)⟧)
      (LL:SET_over_sort⟦constHSET_slice s, T Γ⟧):
  (monadSubstGen_instantiated _ NN) · (monadSubstGen_instantiated _ LL) =
  (mexch_instantiated (Γ1:=constHSET_slice t) (Γ2:=constHSET_slice s) (Γ3:=Γ))
    · (monadSubstGen_instantiated _ (LL · (mweak_instantiated _)))
    · (monadSubstGen_instantiated _ (NN · (monadSubstGen_instantiated _ LL))).
Proof.
  apply subst_interchange_law_gen.
Qed.

(*
(* we were heading for the following lemma that presents the result in terms of the application domain and not category theory: *)
Lemma subst_interchange_law_slice {Γ : SET_over_sort}
      (L : wellsorted_in Γ)
      (N : wellsorted_in (sorted_option_functor (sort_in L) Γ))
      (M : wellsorted_in (sorted_option_functor (sort_in N) (sorted_option_functor (sort_in L) Γ))) :
  subst_slice L (subst_slice N M) =
  subst_slice_eqn (subst_slice L N)
                  (subst_slice_eqn (mweak_slice _ _ L) (mexch_slice M) (mweak_slice_ok _ L))
                  (subst_slice_ok L N).
Proof.
  set (ls := subst_slice L (subst_slice N M)).
  set (rs1 := subst_slice_eqn (mweak_slice _ _ L) (mexch_slice M) (mweak_slice_ok _ L)).
  set (rs2 := subst_slice L N).
  simpl in rs1.

(* Problem: mweak_slice is not an instance of bind_slice, and rewriting is not possible since also *)
(* mweak_slice_ok appears in the term. *)
Admitted.
*)

Context {Γ : SET_over_sort}
      (L : wellsorted_in Γ)
      (N : wellsorted_in (sorted_option_functor (sort_in L) Γ))
      (M : wellsorted_in (sorted_option_functor (sort_in N)
                            (sorted_option_functor (sort_in L) Γ))).

Local Definition LHS : wellsorted_in Γ := subst_slice L (subst_slice N M).
Local Definition RHS : wellsorted_in Γ :=
  subst_slice_eqn (subst_slice L N)
           (subst_slice_eqn (mweak_slice_as_bind_slice _ _ L)
                            (mexch_slice M) (mweak_slice_as_bind_slice_ok _ L))
        (subst_slice_ok L N).

Local Lemma same_sort_LHS_RHS : sort_in LHS = sort_in RHS.
Proof.
  unfold LHS.
  rewrite subst_slice_ok.
  rewrite subst_slice_ok.
  unfold RHS.
  do 2 rewrite subst_slice_eqn_ok.
  apply pathsinv0.
  apply mexch_slice_ok.
Qed.

(*
Lemma subst_interchange_law_slice: LHS = RHS.
Proof.
   unfold LHS.
   do 2 rewrite <- subst_slice_as_bind_slice_agrees.
   unfold subst_slice_as_bind_slice.
   rewrite bind_bind_slice_inst.


(* first treat the question of having the right sort *)
  Focus 2.
    simpl.
  induction a1 as [u | a1].
  + rewrite bind_slice_ok.
    now rewrite postcompWithBinCoproductArrowHSET.
  Focus 2.
  simpl.
  rewrite bind_slice_ok.
   rewrite postcompWithBinCoproductArrowHSET.
   unfold BinCoproductArrow.
   simpl. unfold compose. simpl.
   unfold BinCoproduct_of_functors_ob.
   simpl.
   intermediate_path (sort_in (η_slice(Γ:=BinCoproductObject
          (slice_precat HSET sort has_homsets_HSET)
          (BinCoproducts_HSET_slice sort (constHSET_slice (sort_in L)) Γ))
          a1)).
   Focus 2.
   now rewrite η_slice_ok.
   apply maponpaths. apply idpath.
(* end of verifying the right sort *)

   (* the left-hand side is now of the form bind_slice f' H' M *)
   Admitted.
*)




*)


End MonadInSortToC.
