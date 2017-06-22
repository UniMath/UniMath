(**

    Monads in SET/sort

This file contains the consideration of monads in the slice category SET/sort that are obtained in
our approach to multi-sorted binding signatures. As such, it has nothing to with multi-sorted
binding signatures, but the identifiers refer to that situation.

Written by Ralph Matthes, 2017.

*)

(* Require Import UniMath.Foundations.PartD. *)
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.slicecat.

Local Open Scope cat.

Local Notation "C / X" := (slicecat_ob C X).
Local Notation "C / X" := (slice_precat_data C X).
Local Notation "C / X" := (slice_precat C X (homset_property C)).
Local Notation "C / X ⟦ a , b ⟧" := (slicecat_mor C X a b) (at level 50, format "C / X ⟦ a , b ⟧").


Section MonadsInSET_over_sort.


Variables (sort : hSet).

Definition SET_over_sort : category.
Proof.
exists (SET / sort).
now apply has_homsets_slice_precat.
Defined.

Let hs : has_homsets (SET / sort) := homset_property SET_over_sort.

Let BC := BinCoproducts_slice_precat has_homsets_HSET BinCoproductsHSET sort: BinCoproducts (SET / sort).

(** The object (1,λ _,s) in SET/sort that can be seen as a sorted variable *)
Definition constHSET_slice (s : sort) : SET / sort.
Proof.
exists (TerminalObject TerminalHSET); simpl.
apply (λ x, s).
Defined.

Definition sorted_option_functor (s : sort) : functor (SET / sort) (SET / sort) :=
  constcoprod_functor1 (BinCoproducts_HSET_slice sort) (constHSET_slice s).



(** The following definitions do not depend on the monad coming from our construction, only on the
    slice category we are working in. *)

Local Definition bind_instantiated {T:Monad (SET / sort)}{Γ1 Γ2 : SET_over_sort} (f : SET_over_sort⟦Γ1,T Γ2⟧) :
  SET_over_sort⟦T Γ1,T Γ2⟧ := bind f.

(* the following would be on the right level of generality but make problems later (the monads are not coerced into their underlying functors):
Definition wellsorted_in (T:[SET_over_sort,SET_over_sort])(Γ:SET_over_sort): hSet := pr1(pr1 T Γ).
Definition sort_in (T:[SET_over_sort,SET_over_sort]){Γ:SET_over_sort}(M:wellsorted_in T Γ): sort := pr2 (pr1 T Γ) M.
 *)

Context {T:Monad (SET / sort)}.

Definition wellsorted_in (Γ:SET_over_sort): hSet := pr1(pr1 T Γ).
Definition sort_in {Γ:SET_over_sort}(M:wellsorted_in Γ): sort := pr2 (pr1 T Γ) M.

Definition aux_fh {A1:hSet}{f1:A1->sort}{Γ2:SET_over_sort}
   (f : A1->wellsorted_in Γ2)(H: forall a1:A1, sort_in (f a1) = f1 a1) : SET_over_sort⟦(A1,,f1),T Γ2⟧.
Proof.
   mkpair.
    * exact f.
    * abstract(apply funextsec; intro a1; now apply pathsinv0).
Defined.

Definition bind_slice {A1:hSet}{f1:A1->sort}{Γ2:SET_over_sort}
   (f : A1->wellsorted_in Γ2)(H: forall a1:A1, sort_in (f a1) = f1 a1)(M: wellsorted_in (A1,,f1)) :
   wellsorted_in Γ2.
Proof.
  exact (pr1 (bind_instantiated (aux_fh f H)) M).
Defined.

Lemma bind_slice_ok {A1:hSet}{f1:A1->sort}{Γ2:SET_over_sort}
    (f : A1->wellsorted_in Γ2)(H: forall a1:A1, sort_in (f a1) = f1 a1)(M: wellsorted_in (A1,,f1)) :
    sort_in (bind_slice f H M) = sort_in M.
Proof.
  assert (H1 := pr2 (bind_instantiated (aux_fh f H))).
  apply toforallpaths in H1.
  apply pathsinv0.
  now rewrite H1.
Qed.

Definition η_slice {Γ:SET_over_sort}(a: pr1 (pr1 Γ)) : wellsorted_in Γ :=
  pr1 ((Monads.η T) Γ) a.

Lemma η_slice_ok {Γ:SET_over_sort}(a: pr1 (pr1 Γ)) :
  sort_in (η_slice(Γ:=Γ) a) = (pr2 Γ) a.
Proof.
  unfold η_slice.
  set (H1 := pr2 ((Monads.η T) Γ)).
  simpl in H1.
  apply toforallpaths in H1.
  now rewrite H1.
Qed.

Lemma η_bind_slice {A1:hSet}{f1:A1->sort}{Γ2:SET_over_sort}
      (f : A1->wellsorted_in Γ2)(H: forall a1:A1, sort_in (f a1) = f1 a1)(a1:A1) :
      bind_slice f H (η_slice(Γ:=(A1,,f1)) a1) = f a1.
Proof.
  unfold bind_slice.
  unfold η_slice.
  set (H1 := η_bind(aux_fh f H)).
  apply (maponpaths pr1) in H1.
  apply toforallpaths in H1.
  apply H1.
Qed.

Lemma bind_η_slice {A1:hSet}{f1:A1->sort}(H: forall a1:A1, sort_in (η_slice(Γ:=(A1,,f1)) a1) = f1 a1)(M: wellsorted_in (A1,,f1)) :
  bind_slice (η_slice(Γ:=(A1,,f1))) H M = M.
Proof.
  unfold bind_slice, η_slice.
  unfold bind_instantiated.
  assert (H1 : aux_fh (fun a:A1 => pr1 ((Monads.η T) (A1,, f1)) a) H = (Monads.η T) (A1,, f1)).
  + unfold aux_fh.
    now apply eq_mor_slicecat.
  + intermediate_path (pr1 (bind ((Monads.η T) (A1,, f1))) M).
    * apply (maponpaths (fun f => f M)).
      apply maponpaths.
      apply maponpaths.
      exact H1.
    * now rewrite bind_η.
Qed.
(** notice that the hypothesis [H] can be instantiated with [η_slice_ok] *)

Lemma bind_η_slice_inst {A1:hSet}{f1:A1->sort}(M: wellsorted_in (A1,,f1)) :
  bind_slice (η_slice(Γ:=(A1,,f1))) (η_slice_ok(Γ:=(A1,,f1))) M = M.
Proof.
  apply bind_η_slice.
Qed.
(** would rather be used from right to left *)


Lemma bind_bind_slice {A1:hSet}{f1:A1->sort}{A2:hSet}{f2:A2->sort}{Γ3:SET_over_sort}
  (f : A1->wellsorted_in (A2,,f2))(H1: forall a1:A1, sort_in (f a1) = f1 a1)
  (g : A2->wellsorted_in Γ3)(H2: forall a2:A2, sort_in (g a2) = f2 a2)
  (HH: forall a1:A1, sort_in (bind_slice g H2 (f a1)) = f1 a1)
  (M: wellsorted_in (A1,,f1)) :
    bind_slice g H2 (bind_slice f H1 M) = bind_slice (fun a1:A1 => bind_slice g H2 (f a1)) HH M.
Proof.
  unfold bind_slice.
  intermediate_path (pr1 (bind_instantiated (aux_fh f H1) · bind_instantiated (aux_fh g H2)) M).
  + apply idpath.
  + apply (maponpaths (fun f => f M)).
    apply maponpaths.
    unfold bind_instantiated.
    rewrite bind_bind.
    apply maponpaths.
    now apply eq_mor_slicecat.
Qed.

Local Definition HH_bind_bind_slice {A1:hSet}{f1:A1->sort}{A2:hSet}{f2:A2->sort}{Γ3:SET_over_sort}
  (f : A1->wellsorted_in (A2,,f2))(H1: forall a1:A1, sort_in (f a1) = f1 a1)
  (g : A2->wellsorted_in Γ3)(H2: forall a2:A2, sort_in (g a2) = f2 a2)(a1:A1) :
  sort_in (bind_slice g H2 (f a1)) = f1 a1.
Proof.
  eapply pathscomp0.
  + apply (bind_slice_ok g H2).
  + apply H1.
Defined.

Lemma bind_bind_slice_inst {A1:hSet}{f1:A1->sort}{A2:hSet}{f2:A2->sort}{Γ3:SET_over_sort}
  (f : A1->wellsorted_in (A2,,f2))(H1: forall a1:A1, sort_in (f a1) = f1 a1)
  (g : A2->wellsorted_in Γ3)(H2: forall a2:A2, sort_in (g a2) = f2 a2)
  (HH: forall a1:A1, sort_in (bind_slice g H2 (f a1)) = f1 a1)
  (M: wellsorted_in (A1,,f1)) :
  bind_slice g H2 (bind_slice f H1 M) =
  bind_slice (fun a1:A1 => bind_slice g H2 (f a1)) (HH_bind_bind_slice f H1 g H2) M.
Proof.
  apply bind_bind_slice.
Qed.

(** now we only substitute a single sorted variable *)

Definition aux_inject_N {Γ:SET_over_sort}(N : wellsorted_in Γ):
  SET_over_sort⟦constHSET_slice (sort_in N),T Γ⟧.
Proof.
  mkpair.
  + exact (fun _=> N).
  + now apply funextsec.
Defined.

(* first approach not instantiating from the general situation of a monad:
Definition subst_slice {Γ:SET_over_sort}(N : wellsorted_in Γ)
           (M : wellsorted_in (sorted_option_functor (sort_in N) Γ)): wellsorted_in Γ.
Proof.
  set (aux0 := (CategoryTheory.Monads.η T Γ)).
  set (auxf := BinCoproductArrow _ (BC _ _) (aux_inject_N N) (CategoryTheory.Monads.η T Γ)).
  refine (bind_slice (pr1 auxf) _ M).
  intro a.
  simpl in a.
  induction a as [a | a].
  + now idtac.
  + generalize (ii2(A:=unit) a).
    clear a.
    apply toforallpaths.
(*    intermediate_path ((BinCoproductArrow HSET (BinCoproductsHSET 1%CS (pr1 Γ))
                         (λ _ : unit, N) (pr1 ((Monads.η T) Γ))) ·  (sort_in T)).*)
    change ((BinCoproductArrow HSET (BinCoproductsHSET 1%CS (pr1 Γ))
                                    (λ _ : unit, N) (pr1 ((Monads.η T) Γ))) ·  sort_in =
                 BinCoproductArrow HSET (BinCoproductsHSET 1%CS (pr1 Γ))
                                    (λ _ : unit, sort_in N) (pr2 Γ)).
    rewrite postcompWithBinCoproductArrow.
    apply map_on_two_paths.
    - apply idpath.
    - set (aux1 := pr2 ((Monads.η T) Γ)).
      apply pathsinv0.
      now (etrans; try eapply aux1).
Defined.
 *)

Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)) (at level 50).

Local Definition monadSubstGen_instantiated {T:Monad (SET / sort)}{Γ2 : SET_over_sort}(Γ1: SET_over_sort) (e : SET_over_sort⟦Γ2,T Γ1⟧) :
  SET_over_sort⟦T (Γ2 ⊕ Γ1),T Γ1⟧ := monadSubstGen T BC Γ1 e.

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

Definition subst_slice_as_bind_slice {Γ:SET_over_sort}(N : wellsorted_in Γ)
  (M : wellsorted_in (sorted_option_functor (sort_in N) Γ)): wellsorted_in Γ.
Proof.
  refine (bind_slice (BinCoproductArrow _ (BinCoproductsHSET _ _) (fun _ => N) (η_slice(Γ:=Γ))) _ M).
  abstract(intro a1; induction a1 as [u | a1];
           [apply idpath | unfold BinCoproductArrow; simpl; now rewrite η_slice_ok]).
Defined.

Lemma subst_slice_as_bind_slice_agrees {Γ:SET_over_sort}(N : wellsorted_in Γ)
      (M : wellsorted_in (sorted_option_functor (sort_in N) Γ)) :
  subst_slice_as_bind_slice N M =subst_slice N M.
Proof.
  unfold subst_slice_as_bind_slice, subst_slice.
  unfold bind_slice, monadSubstGen_instantiated.
  apply (maponpaths (fun f => f M)).
  apply maponpaths.
  unfold monadSubstGen, bind_instantiated.
  apply maponpaths.
  now apply eq_mor_slicecat.
Qed.


Definition subst_slice_eqn {Γ:SET_over_sort}(N : wellsorted_in Γ){s : sort}
           (M : wellsorted_in (sorted_option_functor s Γ))(H: sort_in N = s) : wellsorted_in Γ.
Proof.
  apply (subst_slice N).
  now rewrite <- H in M.
Defined.

Lemma subst_slice_eqn_ok {Γ:SET_over_sort}(N : wellsorted_in Γ){s : sort}
      (M : wellsorted_in (sorted_option_functor s Γ))(H: sort_in N = s) :
      sort_in (subst_slice_eqn N M H) = sort_in M.
Proof.
  unfold subst_slice_eqn.
  rewrite subst_slice_ok.
  now rewrite H.
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
  refine (bind_slice (fun a1 => η_slice(Γ:=Γ1 ⊕ Γ2) (pr1 (BinCoproductIn2 _ (BC _ _)) a1)) _ M).
  intro a1.
  now rewrite η_slice_ok.
Defined.

Lemma mweak_slice_as_bind_slice_agrees (Γ1 : SET_over_sort){Γ2 : SET_over_sort}(M : wellsorted_in Γ2) :
  mweak_slice_as_bind_slice Γ1 Γ2 M = mweak_slice Γ1 Γ2 M.
Proof.
  unfold mweak_slice_as_bind_slice, mweak_slice.
  unfold bind_slice, mweak_instantiated.
  apply (maponpaths (fun f => f M)).
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
  refine (bind_slice ((BinCoproductArrow _ _ a1 (BinCoproductArrow _ _ a21 a22)) · η_slice(Γ:=Γ2 ⊕ (Γ1 ⊕ Γ3))) _ M).
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
  apply (maponpaths (fun f => f M)).
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


(* we were heading for the following lemma that presents the result in terms of the application domain and not category theory:

Lemma subst_interchange_law_slice {Γ : SET_over_sort}
      (L : wellsorted_in Γ)
      (N : wellsorted_in (sorted_option_functor (sort_in L) Γ))
      (M : wellsorted_in (sorted_option_functor (sort_in N) (sorted_option_functor (sort_in L) Γ))) :
  subst_slice L (subst_slice N M) =
  subst_slice_eqn (subst_slice L N)
                  (subst_slice_eqn (mweak_slice _ L) (mexch_slice M) (mweak_slice_ok _ L))
                  (subst_slice_ok L N).
Proof.
  set (ls := subst_slice L (subst_slice N M)).
  set (rs1 := subst_slice_eqn (mweak_slice _ L) (mexch_slice M) (mweak_slice_ok _ L)).
  set (rs2 := subst_slice L N).
  simpl in rs1.

Problem: mweak_slice is not an instance of bind_slice, and rewriting is not possible since also
mweak_slice_ok appears in the term.
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
  unfold subst_slice.
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
*)

(*
Lemma subst_interchange_law_slice: LHS = RHS.
Proof.
   unfold RHS.
   unfold subst_slice_eqn at 1.
   rewrite <- mexch_slice_as_bind_slice_agrees.
   unfold mexch_slice_as_bind_slice at 1.
   unfold subst_slice, subst_slice_eqn, mweak_slice_as_bind_slice.
   unfold subst_slice.
   simpl.

*)








End MonadsInSET_over_sort.
