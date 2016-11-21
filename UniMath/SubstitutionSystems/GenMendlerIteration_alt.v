Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.yoneda.
(* Require Import UniMath.CategoryTheory.equivalences. (* for adjunctions *) *)
(* Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq. (* for alternative reading of adj *) *)
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.whiskering.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "↓ f" := (mor_from_algebra_mor _ _ _ f) (at level 3, format "↓ f").
Local Notation "'chain'" := (diagram nat_graph).

(** Goal: derive Generalized Iteration in Mendler-style and a fusion law *)

(** * Generalized Iteration in Mendler-style *)
Section GenMenIt.

Context {C : precategory} (hsC : has_homsets C) (IC : Initial C)
        (CC : Colims_of_shape nat_graph C) (F : functor C C)
        (HF : is_omega_cocont F).

Local Notation "0" := (InitialObject IC).

Let AF := FunctorAlg F hsC.
Let chnF := initChain IC F.

Definition μF_Initial : Initial AF := colimAlgInitial hsC IC HF (CC chnF).

Let μF : C := alg_carrier _ (InitialObject μF_Initial).
Let inF : C⟦F μF,μF⟧ := alg_map _ (InitialObject μF_Initial).
Local Definition e : Π (n : nat), C⟦iter_functor F n IC,μF⟧ := colimIn (CC chnF).

Definition cocone_μF : cocone chnF μF := colimCocone (CC chnF).

(* Let FchnF := mapdiagram F chnF. *)

(* Lemma cocone_F : cocone FchnF (F μF). *)
(* Proof. *)
(* use mk_cocone. *)
(* - intros n. *)
(*   apply (# F (e n)). *)
(* - intros m n e. *)
(*   simpl. rewrite <- functor_comp. *)
(*   generalize (coconeInCommutes cocone_μF m n e). *)
(*   cbn. *)
(*   destruct e. *)
(*   simpl. *)
(*   unfold e. *)
(*   unfold colimIn. *)
(*   unfold cocone_μF. *)
(*   intros HH. *)
(*   apply maponpaths. *)
(*   apply HH. *)
(* Defined. *)

(* Lemma cocone_F' : cocone FchnF μF. *)
(* Proof. *)
(* use mk_cocone. *)
(* - intros n. *)
(*   apply (e (S n)). *)
(* - intros m n []; clear n. *)
(*   apply (coconeInCommutes (colimCocone (CC chnF)) (S m) _ (idpath _)). *)
(* Defined. *)

Lemma e_comm (n : nat) : e (S n) = # F (e n) ;; inF.
Proof.
apply pathsinv0, (colimArrowCommutes (mk_ColimCocone _ _ _ (HF _ _ _ (isColimCocone_from_ColimCocone (CC chnF))))).
Qed.

Context {D : precategory} (hsD : has_homsets D).

Section the_iteration_principle.

Variables (X : D) (L : functor C D).
Hypothesis (IL : isInitial D (L 0)) (HL : is_omega_cocont L).

Let ILD : Initial D := tpair _ _ IL.
Local Notation "'L0'" := (InitialObject ILD).

Let Yon : functor D^op HSET := yoneda_objects D hsD X.

Definition ψ_source : functor C^op HSET := functor_composite (functor_opp L) Yon.
Definition ψ_target : functor C^op HSET := functor_composite (functor_opp F) ψ_source.

Section general_case.


Variable ψ : ψ_source ⟶ ψ_target.

Let LchnF : chain D := mapchain L chnF.

(* Definition iter_functor' {C' : precategory} (F' : functor C' C') (n : nat) : functor C' C'. *)
(* Proof. *)
(*   induction n as [ | n IHn]. *)
(*   - apply functor_identity. *)
(*   - apply (functor_composite F' IHn). *)
(* Defined. *)

Definition Pow_source : functor C^op HSET := ψ_source.
Definition Pow_target (n : nat) : functor C^op HSET :=
  functor_composite (functor_opp (iter_functor F n)) ψ_source.

Definition Pow (n : nat) : Pow_source ⟶ Pow_target n.
Proof.
induction n as [|n Pown].
- apply nat_trans_id.
- apply (nat_trans_comp Pown (pre_whisker (functor_opp (iter_functor F n)) ψ)).
Defined.

Lemma PowSn (n : nat) : Pow (S n) = nat_trans_comp (Pow n) (pre_whisker (functor_opp (iter_functor F n)) ψ).
Proof.
apply idpath.
Qed.

Local Definition z : D⟦L0,X⟧ := InitialArrow ILD X.

Lemma Pow_cocone_subproof n :
  dmor LchnF (idpath (S n)) ;; pr1 (Pow (S n)) IC z = pr1 (Pow n) IC z.
Proof.
induction n as [|n IHn].
+ cbn.
  apply (InitialArrowUnique ILD).
+ change (pr1 (Pow (S (S n))) _ z) with (ψ (iter_functor F (S n) 0) (Pow (S n) _ z)).
  assert (H : dmor LchnF (idpath (S (S n))) ;; ψ ((iter_functor F (S n)) IC) ((Pow (S n)) IC z) =
              ψ (iter_functor F n 0) (dmor LchnF (idpath (S n)) ;; pr1 (Pow (S n)) _ z)).
    apply pathsinv0, (toforallpaths _ _ _ (nat_trans_ax ψ _ _ (dmor chnF (idpath (S n))))).
  now rewrite H, IHn.
Qed.

Definition Pow_cocone : cocone LchnF X.
Proof.
use mk_cocone.
- intro n.
  apply (pr1 (Pow n) _ z).
- abstract (intros n m []; clear m; apply Pow_cocone_subproof).
Defined.

Definition temp : ColimCocone LchnF.
Proof.
use mk_ColimCocone.
- apply (L μF).
- apply (mapcocone L _ cocone_μF).
- apply HL, (isColimCocone_from_ColimCocone (CC chnF)).
Defined.

Definition preIt : D⟦L μF,X⟧.
Proof.
apply (@colimArrow D nat_graph LchnF temp X Pow_cocone).
Defined.

Lemma eqSS n : # L (e n) ;; preIt = Pow n IC z.
Proof.
apply (colimArrowCommutes temp).
Qed.

Lemma is_iso_inF : is_iso inF.
Proof.
(* Use Lambek's lemma, this could be extracted from the concrete proof as well *)
apply (initialAlg_is_iso _ hsC), pr2.
Defined.

Let inF_iso : iso (F μF) μF := isopair _ is_iso_inF.
Let inF_inv : C⟦μF,F μF⟧ := inv_from_iso inF_iso.

(* The direction ** -> * *)
Lemma SS_imp_S (H : Π n, # L (e n) ;; preIt = Pow n IC z) : # L inF ;; preIt = ψ μF preIt.
Proof.
assert (H' : Π n, # L (e (S n)) ;; # L inF_inv ;; ψ μF preIt = pr1 (Pow (S n)) _ z).
{ intro n.
  rewrite e_comm, functor_comp.
  eapply pathscomp0.
  eapply cancel_postcomposition.
  rewrite <-assoc.
  eapply maponpaths.
  rewrite <- functor_comp.
  generalize (iso_inv_after_iso inF_iso).
  simpl.
  intros XXX.
  eapply maponpaths.
  apply XXX.
  rewrite functor_id.
  rewrite id_right.
  assert (H1 : # L (# F (e n)) ;; ψ μF preIt = ψ (iter_functor F n 0) (# L (e n) ;; preIt)).
      apply pathsinv0, (toforallpaths _ _ _ (nat_trans_ax ψ _ _ (e n))).
  eapply pathscomp0. apply H1.
  rewrite H.
  apply idpath.
}
assert (HH : preIt = # L inF_inv ;; ψ μF preIt).
apply pathsinv0.
(* transparent assert (apa : (iso (L (F μF)) (L μF))). *)
(* apply (isopair (# L inF)), functor_on_iso_is_iso. *)
(* apply pathsinv0, (@iso_inv_to_left _ _ _ _ apa preIt (ψ μF preIt)). *)

apply (colimArrowUnique temp); simpl; intro n.
destruct n.
- apply (InitialArrowUnique ILD).
- simpl.
  eapply pathscomp0.
  Focus 2.
  apply H'.
  rewrite assoc.
  apply idpath.
- eapply pathscomp0. eapply maponpaths.
  apply HH.
  rewrite assoc, <- functor_comp.
  unfold inF_inv.
  generalize (iso_inv_after_iso inF_iso).
  simpl.
  intros XXX.
  rewrite XXX.
  now rewrite functor_id, id_left.
Qed.

(* General version, not needed? *)
(* Lemma SS_imp_S h (H : Π n, # L (e n) ;; h = Pow n IC z) : # L inF ;; h = ψ μF h. *)
(* Proof. *)
(* assert (H' : Π n, # L (e (S n)) ;; # L inF_inv ;; ψ μF h = pr1 (Pow (S n)) _ z). *)
(* admit. *)
(* generalize (@colimArrowUnique D nat_graph LchnF temp X). *)
(* Check (# L inF_inv ;; ψ μF h). *)
(* Check (# L inF). *)
(* transparent assert (apa : (iso (L (F μF)) (L μF))). *)
(* apply (isopair (# L inF)), functor_on_iso_is_iso. *)
(* apply pathsinv0, (@iso_inv_to_left _ _ _ _ apa h (ψ μF h)). *)
(* Check colimArrowUnique. *)
(* Qed. *)


(* The direction * -> ** *)
Lemma S_imp_SS h n : # L inF ;; h = ψ μF h → # L (e n) ;; h = Pow n IC z.
Proof.
intros Hh.
induction n.
- cbn.
  apply (InitialArrowUnique ILD).
- rewrite e_comm, functor_comp, <- assoc, Hh.
  assert (H : # L (# F (e n)) ;; ψ μF h = ψ (iter_functor F n 0) (# L (e n) ;; h)).
    apply pathsinv0, (toforallpaths _ _ _ (nat_trans_ax ψ _ _ (e n))).
  now rewrite H, IHn.
Qed.

Lemma preIt_ok : # L inF ;; preIt = ψ μF preIt.
Proof.
apply SS_imp_S; intro n; apply eqSS.
Qed.

Lemma preIt_uniq (t : Σ h, # L inF ;; h = ψ μF h) : t = (preIt,,preIt_ok).
Proof.
apply subtypeEquality.
- intros f; apply hsD.
- simpl.
  destruct t as [f Hf]; simpl.
  unfold preIt.
  apply (colimArrowUnique temp); intro n.
  simpl.
  apply S_imp_SS.
  apply Hf.
Qed.

Theorem GenMendlerIteration : ∃! (h : L μF --> X), #L inF ;; h = ψ μF h.
Proof.
mkpair.
- apply (preIt,,preIt_ok).
- exact preIt_uniq.
Defined.

Definition It : L μF --> X := pr1 (pr1 GenMendlerIteration).

Lemma It_is_preIt : It = preIt.
Proof.
  apply idpath.
Qed.

End general_case.

(** * Specialized Mendler Iteration *)
Section special_case.

Variables (G : functor D D) (ρ : G X --> X).
Variables (θ : functor_composite F L ⟶ functor_composite L G).

Lemma is_nat_trans_ψ_from_comps :
        is_nat_trans ψ_source ψ_target
          (λ A (f : yoneda_objects_ob D X (L A)), θ A ;; # G f ;; ρ).
Proof.
intros A B h; apply funextfun; intro f; cbn.
rewrite functor_comp, !assoc.
assert (θ_nat_trans_ax := nat_trans_ax θ); simpl in θ_nat_trans_ax.
now rewrite <- θ_nat_trans_ax.
Qed.

Definition ψ_from_comps : ψ_source ⟶ ψ_target.
Proof.
mkpair.
- intros A f.
  exact (θ A ;; #G f ;; ρ).
- apply is_nat_trans_ψ_from_comps.
Defined.

Definition SpecialGenMendlerIteration :
  ∃! (h : L μF --> X), # L inF ;; h = θ μF ;; #G h ;; ρ
    := GenMendlerIteration ψ_from_comps.

End special_case.
End the_iteration_principle.

(** * Fusion law for Generalized Iteration in Mendler-style *)
Section fusion_law.

Variables (X X' : D).

Let Yon : functor D^op HSET := yoneda_objects D hsD X.
Let Yon' : functor D^op HSET := yoneda_objects D hsD X'.

Variables (L : functor C D) (HL : is_omega_cocont L) (IL : isInitial D (L 0)).
Variables (ψ : ψ_source X L ⟶ ψ_target X L).

Variables (L' : functor C D) (HL' : is_omega_cocont L') (IL' : isInitial D (L' 0)).
Variables (ψ' : ψ_source X' L' ⟶ ψ_target X' L').

Variables (Φ : functor_composite (functor_opp L) Yon ⟶ functor_composite (functor_opp L') Yon').

Variables (H : ψ μF ;; Φ (F μF) = Φ μF ;; ψ' μF).

Theorem fusion_law : Φ μF (It X L IL HL ψ) = It X' L' IL' HL' ψ'.
Proof.
apply path_to_ctr.
assert (Φ_is_nat := nat_trans_ax Φ).
assert (Φ_is_nat_inst1 := Φ_is_nat _ _ inF).
assert (Φ_is_nat_inst2 := toforallpaths _ _ _ Φ_is_nat_inst1 (It X L IL HL ψ)).
unfold compose in Φ_is_nat_inst2; simpl in Φ_is_nat_inst2.
simpl.
rewrite <- Φ_is_nat_inst2.
assert (H_inst :=  toforallpaths _ _ _ H (It X L IL HL ψ)).
unfold compose in H_inst; simpl in H_inst.
rewrite <- H_inst.
apply maponpaths.
rewrite It_is_preIt.
apply preIt_ok.
Qed.

End fusion_law.
End GenMenIt.


(********* OLD STUFF *)
(** * Generalized Iteration in Mendler-style *)

(* Section GenMenIt. *)

(* Variable C : precategory. *)
(* Variable hsC : has_homsets C. *)

(* Variable F : functor C C. *)

(* Let AF := FunctorAlg F hsC. *)

(* Definition AlgConstr (A : C) (α : F A --> A) : AF. *)
(* Proof. *)
(*   exists A. *)
(*   exact α. *)
(* Defined. *)

(* Notation "⟨ A , α ⟩" := (AlgConstr A α). *)
(* (* \<  , \> *) *)

(* Variable μF_Initial : Initial AF. *)

(* Let μF : C := alg_carrier _ (InitialObject μF_Initial). *)
(* Let inF : F μF --> μF := alg_map _ (InitialObject μF_Initial). *)

(* Let iter {A : C} (α : F A --> A) : μF --> A := *)
(*   ↓(InitialArrow μF_Initial ⟨A,α⟩). *)

(* Variable C' : precategory. *)
(* Variable hsC' : has_homsets C'. *)


(* Section the_iteration_principle. *)

(* Variable X : C'. *)

(* Let Yon : functor C'^op HSET := yoneda_objects C' hsC' X. *)

(* Variable L : functor C C'. *)

(* Variable is_left_adj_L : is_left_adjoint L. *)

(* Let φ := @φ_adj _ _ _ is_left_adj_L. *)
(* Let φ_inv := @φ_adj_inv _ _ _ is_left_adj_L. *)
(* Let R : functor _ _ := right_adjoint is_left_adj_L. *)
(* Let η : nat_trans _ _ := unit_from_left_adjoint is_left_adj_L. *)
(* Let ε : nat_trans _ _ := counit_from_left_adjoint is_left_adj_L. *)
(* (* Let φ_natural_precomp := @φ_adj_natural_precomp _ _ _ is_left_adj_L. *)
(* Let φ_inv_natural_precomp := @φ_adj_inv_natural_precomp _ _ _ is_left_adj_L. *)
(* Let φ_after_φ_inv := @φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L. *)
(* Let φ_inv_after_φ := @φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L.*) *)


(* Arguments φ {_ _} _ . *)
(* Arguments φ_inv {_ _} _ . *)

(* Definition ψ_source : functor C^op HSET := functor_composite (functor_opp L) Yon. *)
(* Definition ψ_target : functor C^op HSET := functor_composite (functor_opp F) ψ_source. *)

(* Section general_case. *)

(* Variable ψ : ψ_source ⟶ ψ_target. *)

(* Definition preIt : L μF --> X := φ_inv (iter (φ (ψ (R X) (ε X)))). *)


(* Lemma ψ_naturality (A B: C)(h: B --> A)(f: L A --> X): ψ B (#L h;; f) = #L (#F h);; ψ A f. *)
(* Proof. *)
(*   assert (ψ_is_nat := nat_trans_ax ψ); *)
(*   assert (ψ_is_nat_inst1 := ψ_is_nat _ _ h). *)
(*   (* assert (ψ_is_nat_inst2 := aux0 _ _ _ _ f ψ_is_nat_inst1). *) *)
(*   assert (ψ_is_nat_inst2 := toforallpaths _ _ _ ψ_is_nat_inst1 f). *)
(*   apply ψ_is_nat_inst2. *)
(* Qed. *)

(* Lemma truth_about_ε (A: C'): ε A = φ_inv (identity (R A)). *)
(* Proof. *)
(*   unfold φ_inv, φ_adj_inv. *)
(*   rewrite functor_id. *)
(*   apply pathsinv0. *)
(*   apply id_left. *)
(* Qed. *)

(* Lemma φ_ψ_μF_eq (h: L μF --> X): φ (ψ μF h) = #F (φ h) ;; φ(ψ (R X) (ε X)). *)
(* Proof. *)
(*   rewrite <- φ_adj_natural_precomp. *)
(*   apply maponpaths. *)
(*   eapply pathscomp0. *)
(* Focus 2. *)
(*   apply ψ_naturality. *)
(*   apply maponpaths. *)
(*   rewrite truth_about_ε. *)
(*   rewrite <- (φ_adj_inv_natural_precomp _ _ _ is_left_adj_L). *)
(*   rewrite id_right. *)
(*   apply pathsinv0. *)
(*   change (φ_inv(φ h) = h). *)
(*   apply φ_adj_inv_after_φ_adj. *)
(* Qed. *)

(* Lemma cancel_φ {A: C}{B: C'} (f g : L A --> B): φ f = φ g -> f = g. *)
(* Proof. *)
(*   intro Hyp. *)
(* (* pedestrian way: *)
(*   rewrite <- (φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L f). *)
(*   rewrite <- (φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L g). *)
(*   apply maponpaths. *)
(*   exact Hyp. *)
(* *) *)
(*   apply (invmaponpathsweq (adjunction_hom_weq _ _ _ is_left_adj_L _ _)). *)
(*   exact Hyp. *)
(* Qed. *)

(* Lemma preIt_ok : # L inF;; preIt = ψ μF preIt. *)
(* Proof. *)
(*     apply cancel_φ. *)
(*     rewrite φ_ψ_μF_eq. *)
(*     rewrite (φ_adj_natural_precomp _ _ _ is_left_adj_L). *)
(*     unfold preIt. *)
(*     rewrite φ_adj_after_φ_adj_inv. *)
(*     rewrite (φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L). *)
(*     assert (iter_eq := algebra_mor_commutes _ _ _ (InitialArrow μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)). *)
(*     exact iter_eq. *)
(* Qed. *)

(* Lemma preIt_uniq (t : Σ h : L μF --> X, # L inF;; h = ψ μF h): *)
(*     t = tpair (λ h : L μF --> X, # L inF;; h = ψ μF h) preIt preIt_ok. *)
(* Proof. *)
(*     destruct t as [h h_rec_eq]; simpl. *)
(*     assert (same: h = preIt). *)
(* Focus 2. *)
(*     apply subtypeEquality. *)
(*     + intro. *)
(*       simpl. *)
(*       apply hsC'. *)
(* Focus 2. *)
(*     simpl. *)
(*     exact same. *)

(*     apply cancel_φ. *)
(*     unfold preIt. *)
(*     rewrite (φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L). *)
(*     (* assert (iter_uniq := algebra_mor_commutes _ _ _ *) *)
(*     (*                        (InitialArrow μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)). *) *)
(*     (* simpl in iter_uniq. *) *)
(*     assert(φh_is_alg_mor: inF ;; φ h = #F(φ h) ;; φ (ψ (R X) (ε X))). *)
(*       (* remark: I am missing a definition of the algebra morphism property in UniMath.CategoryTheory.FunctorAlgebras *) *)
(*     + rewrite <- φ_ψ_μF_eq. *)
(*       rewrite <- φ_adj_natural_precomp. *)
(*       apply maponpaths. *)
(*       exact h_rec_eq. *)
(*     + (* set(φh_alg_mor := tpair _ _ φh_is_alg_mor : pr1 μF_Initial --> ⟨ R X, φ (ψ (R X) (ε X)) ⟩). *) *)
(*        simple refine (let X : AF ⟦ InitialObject μF_Initial, ⟨ R X, φ (ψ (R X) (ε X)) ⟩ ⟧ := _ in _). *)
(*        * apply (tpair _ (φ h)); assumption. *)
(*        * apply (maponpaths pr1 (InitialArrowUnique _ _ X0)). *)
(* Qed. *)

(* Theorem GenMendlerIteration : iscontr (Σ h : L μF --> X, #L inF ;; h = ψ μF h). *)
(* Proof. *)
(*   simple refine (tpair _ _ _ ). *)
(*   - exists preIt. *)
(*     exact preIt_ok. *)
(*   - exact preIt_uniq. *)
(* Defined. *)

(* Definition It : L μF --> X := pr1 (pr1 GenMendlerIteration). *)
(* Lemma It_is_preIt : It = preIt. *)
(* Proof. *)
(*   apply idpath. *)
(* Qed. *)

(* End general_case. *)

(* (** * Specialized Mendler Iteration *) *)

(* Section special_case. *)

(*   Variable G : functor C' C'. *)
(*   Variable ρ : G X --> X. *)
(*   Variable θ : functor_composite F L ⟶ functor_composite L G. *)


(*   Lemma is_nat_trans_ψ_from_comps *)
(*         :  is_nat_trans ψ_source ψ_target *)
(*                         (λ (A : C^op) (f : yoneda_objects_ob C' X (L A)), θ A;; # G f;; ρ). *)
(*   Proof. *)
(*     intros A B h. *)
(*       apply funextfun. *)
(*       intro f. *)
(*       simpl. *)
(*       unfold compose at 1 5; simpl. *)
(*       rewrite functor_comp. *)
(*       repeat rewrite assoc. *)
(*       assert (θ_nat_trans_ax := nat_trans_ax θ). *)
(*       unfold functor_composite in θ_nat_trans_ax. *)
(*       simpl in θ_nat_trans_ax. *)
(*       rewrite <- θ_nat_trans_ax. *)
(*       apply idpath. *)
(*    Qed. *)

(*   Definition ψ_from_comps : ψ_source ⟶ ψ_target. *)
(*   Proof. *)
(*     simple refine (tpair _ _ _ ). *)
(*     - intro A. simpl. intro f. *)
(*       unfold yoneda_objects_ob in *. *)
(*       exact (θ A ;; #G f ;; ρ). *)
(*     - apply is_nat_trans_ψ_from_comps. *)
(*   Defined. *)


(*   Definition SpecialGenMendlerIteration : *)
(*     iscontr *)
(*       (Σ h : L μF --> X, # L inF ;; h = θ μF ;; #G h ;; ρ) *)
(*     := GenMendlerIteration ψ_from_comps. *)

(* End special_case. *)

(* End the_iteration_principle. *)

(* (** * Fusion law for Generalized Iteration in Mendler-style *) *)

(* Variable X X': C'. *)
(* Let Yon : functor C'^op HSET := yoneda_objects C' hsC' X. *)
(* Let Yon' : functor C'^op HSET := yoneda_objects C' hsC' X'. *)
(* Variable L : functor C C'. *)
(* Variable is_left_adj_L : is_left_adjoint L. *)
(* Variable ψ : ψ_source X L ⟶ ψ_target X L. *)
(* Variable L' : functor C C'. *)
(* Variable is_left_adj_L' : is_left_adjoint L'. *)
(* Variable ψ' : ψ_source X' L' ⟶ ψ_target X' L'. *)

(* Variable Φ : functor_composite (functor_opp L) Yon ⟶ functor_composite (functor_opp L') Yon'. *)

(* Section fusion_law. *)

(*   Variable H : ψ μF ;; Φ (F μF) = Φ μF ;; ψ' μF. *)

(*   Theorem fusion_law : Φ μF (It X L is_left_adj_L ψ) = It X' L' is_left_adj_L' ψ'. *)
(*   Proof. *)
(*     apply pathsinv0. *)
(*     apply pathsinv0. *)
(*     apply path_to_ctr. *)
(*     assert (Φ_is_nat := nat_trans_ax Φ). *)
(*     assert (Φ_is_nat_inst1 := Φ_is_nat _ _ inF). *)
(*     assert (Φ_is_nat_inst2 := toforallpaths _ _ _ Φ_is_nat_inst1 (It X L is_left_adj_L ψ)). *)
(*     unfold compose in Φ_is_nat_inst2; simpl in Φ_is_nat_inst2. *)
(*     simpl. *)
(*     rewrite <- Φ_is_nat_inst2. *)
(*     assert (H_inst :=  toforallpaths _ _ _ H (It X L is_left_adj_L ψ)). *)
(*     unfold compose in H_inst; simpl in H_inst. *)
(*     rewrite <- H_inst. *)
(*     apply maponpaths. *)
(*     rewrite It_is_preIt. *)
(*     apply preIt_ok. *)
(*   Qed. *)

(* End fusion_law. *)



(* End GenMenIt. *)
