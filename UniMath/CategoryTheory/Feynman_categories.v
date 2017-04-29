(** Anthony Bordg, April 2017 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.


(** * Monoidal (pre)category *)


Definition binprod_precat (C D : precategory) : precategory.
Proof.
  refine (product_precategory bool _).
  intro x. induction x.
  - exact C.
  - exact D.
Defined.

Notation "C × D" := (binprod_precat C D) : cat.

Local Open Scope cat.

Definition binprod_precat_pair_of_el {C D : precategory} (a : C) (b : D) : ob (C × D).
Proof.
  intro x. induction x.
  - exact a.
  - exact b.
Defined.

Notation "( a , b )" := (binprod_precat_pair_of_el a b) : cat.

Definition binprod_precat_pair_of_mor {C D : precategory} {a c : C} {b d : D} (f : a --> c) (g : b --> d) : (a , b) --> (c , d).
Proof.
  intro x. induction x.
  - exact f.
  - exact g.
Defined.

Notation "( f #, g )" := (binprod_precat_pair_of_mor f g) : cat.

Lemma id_binprod_precat {C : precategory} (a b : C) : identity (a , b) = (identity a #, identity b).
Proof.
  apply funextsec.
  intro x. induction x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Defined.

Lemma comp_binprod_precat {C : precategory} {u v x y z w : C} (f : u --> x) (g : v --> y) (h : x --> z) (i : y --> w) :
  (f #, g) · (h #, i) = (f · h #, g · i).
Proof.
  intros.
  apply funextsec. intro b.
  induction b.
  - cbn. reflexivity.
  - cbn. reflexivity.
Defined.

(** Definition of natural isomorphisms *)

Definition is_nat_iso {C C' : precategory_data}
  (F F' : functor_data C C')
  (t : ∏ x : ob C, iso (F x)  (F' x)) :=
  ∏ (x x' : ob C)(f : x --> x'),
    # F f · t x' = t x · #F' f.

Definition nat_iso {C C' : precategory_data} (F F' : functor_data C C') : UU :=
  total2 (fun t : ∏ x : ob C, iso (F x)  (F' x) => is_nat_iso F F' t).

Notation "F ⇔ G" := (nat_iso F G) (at level 39) : cat.
(* to input: type "\<=>" with Agda input method *)

Definition nat_iso_to_nat_trans {C' C'' : precategory_data} (F' F'' : functor_data C' C'') (α : F' ⇔ F'') : F' ⟹ F''.
Proof.
  use tpair.
  - exact (pr1 α).
  - exact (pr2 α).
Defined.

Coercion nat_iso_to_nat_trans : nat_iso >-> nat_trans.


Section monoidal_precategory.

Variable C : precategory.
Variable F : (C × C) ⟶ C.

Notation "a ⊗ b" := (F (a , b)) (at level 30, right associativity) : cat.
(** use \ox with Agda input mode *)

Notation "f #⊗ g" := (#F (f #, g)) (at level 30, right associativity) : cat.

Definition F0_on_ob : ob ((C × C) × C) -> ob C.
Proof.
 intro f.
 exact (f true true ⊗ (f true false ⊗ f false)).
Defined.

Definition F0_on_mor : ∏  f g : ob ((C × C) × C), f --> g -> F0_on_ob f --> F0_on_ob g.
Proof.
  intros f g h.
  exact (h true true #⊗ (h true false #⊗ h false)).
Defined.

Definition F0_data : functor_data ((C × C) × C) C := functor_data_constr ((C × C) × C) C F0_on_ob F0_on_mor.

Definition F0_idax : functor_idax F0_data.
Proof.
  intro f.
  unfold F0_data, F0_on_ob, F0_on_mor. cbn.
  rewrite <- (id_binprod_precat).
  rewrite (pr1 (pr2 F)).
  rewrite <- id_binprod_precat.
  apply (pr1 (pr2 F)).
Defined.

Definition F0_compax : functor_compax F0_data.
Proof.
  intros a b c f g.
  unfold F0_data, functor_data_constr, F0_on_mor. cbn.
  rewrite <- (comp_binprod_precat ).
  rewrite (pr2 (pr2 F)).
  rewrite <- (comp_binprod_precat).
  apply (pr2 (pr2 F)).
Defined.

Definition isfunctor_F0_data : is_functor F0_data := dirprodpair F0_idax F0_compax.

Definition F0 : functor ((C × C) × C) C := tpair _ F0_data isfunctor_F0_data.

Definition F1_on_ob : ob ((C × C) × C) -> ob C.
Proof.
 intro f.
 exact ((f true true ⊗ f true false) ⊗ f false).
Defined.

Definition F1_on_mor : ∏  f g : ob ((C × C) × C), f --> g -> F1_on_ob f --> F1_on_ob g.
Proof.
  intros f g h.
  exact ((h true true #⊗ h true false) #⊗ h false).
Defined.

Definition F1_data : functor_data ((C × C) × C) C := functor_data_constr ((C × C) × C) C F1_on_ob F1_on_mor.

Definition F1_idax : functor_idax F1_data.
Proof.
  intro f.
  unfold F1_data, F1_on_ob, F1_on_mor. cbn.
  rewrite <- id_binprod_precat.
  rewrite (pr1 (pr2 F)).
  transitivity (#F (identity ((pr1 F) (f true true, f true false) , f false))).
  - apply (maponpaths #F).
    symmetry.
    apply id_binprod_precat.
  - apply (pr1 (pr2 F)).
Defined.

Definition F1_compax : functor_compax F1_data.
Proof.
  intros a b c f g.
  unfold F1_data, functor_data_constr, F1_on_mor. cbn.
  rewrite <- (comp_binprod_precat ).
  transitivity (#F ((#F (f true true #, f true false)  #, f false) · (#F (g true true #, g true false) #, g false))).
  - rewrite (pr2 (pr2 F)).
    rewrite <- (comp_binprod_precat).
    reflexivity.
  - apply (pr2 (pr2 F)).
Defined.

Definition isfunctor_F1_data : is_functor F1_data := dirprodpair F1_idax F1_compax.

Definition F1 : functor ((C × C) × C) C := tpair _ F1_data isfunctor_F1_data.

Definition associator : UU := nat_iso F0 F1.

Definition pentagon_identity (α : associator) :=
  ∏ a b c d : C, (inv_from_iso (pr1 α ((a , b) , c)) #⊗ identity d) ∘ (pr1 α (((a ⊗ b) , c) , d)) ∘ (pr1 α ((a , b) , c ⊗ d)) =
                 (pr1 α ((a , b ⊗ c) , d)) ∘ (identity a #⊗ pr1 α ((b , c) , d)).

Definition F_true_on_ob (e : C) : ob C -> ob C.
Proof.
  intro c.
  exact (e ⊗ c).
Defined.

Definition F_true_on_mor (e : C) : ∏  c d : ob C, c --> d -> F_true_on_ob e c --> F_true_on_ob e d.
Proof.
  intros c d f.
  exact (identity e #⊗ f).
Defined.

Definition F_true_data (e : C) : functor_data C C := functor_data_constr C C (F_true_on_ob e) (F_true_on_mor e).

Definition F_true_idax (e : C) : functor_idax (F_true_data e).
Proof.
  intro c.
  unfold F_true_data, F_true_on_ob, F_true_on_mor. cbn.
  rewrite <- id_binprod_precat.
  apply (pr1 (pr2 F)).
Defined.

Definition F_true_compax (e : C) : functor_compax (F_true_data e).
Proof.
  intros a b c f g.
  unfold F_true_data, F_true_on_ob, F_true_on_mor. cbn.
  rewrite <- (pr2 (pr2 F)).
  apply maponpaths.
  symmetry.
  rewrite comp_binprod_precat.
  rewrite (id_left).
  reflexivity.
Defined.

Definition isfunctor_F_true_data (e : C) : is_functor (F_true_data e) := dirprodpair (F_true_idax e) (F_true_compax e).

Definition F_true (e : C) : functor C C := tpair _ (F_true_data e) (isfunctor_F_true_data e).

Definition Id {C : precategory} := functor_identity C.

Definition left_unitor (e : C) : UU := F_true e ⇔ Id.

Definition F_false_on_ob (e : C) : ob C -> ob C.
Proof.
  intro c.
  exact (c ⊗ e).
Defined.

Definition F_false_on_mor (e : C) : ∏  c d : ob C, c --> d -> F_false_on_ob e c --> F_false_on_ob e d.
Proof.
  intros c d f.
  exact (f #⊗ identity e).
Defined.

Definition F_false_data (e : C) : functor_data C C := functor_data_constr C C (F_false_on_ob e) (F_false_on_mor e).

Definition F_false_idax (e : C) : functor_idax (F_false_data e).
Proof.
  intro c.
  unfold F_false_data, F_false_on_ob, F_false_on_mor. cbn.
  rewrite <- id_binprod_precat.
  apply (pr1 (pr2 F)).
Defined.

Definition F_false_compax (e : C) : functor_compax (F_false_data e).
Proof.
  intros a b c f g.
  unfold F_false_data, F_false_on_ob, F_false_on_mor. cbn.
  rewrite <- (pr2 (pr2 F)).
  apply maponpaths.
  symmetry.
  rewrite comp_binprod_precat.
  rewrite (id_left).
  reflexivity.
Defined.

Definition isfunctor_F_false_data (e : C) : is_functor (F_false_data e) := dirprodpair (F_false_idax e) (F_false_compax e).

Definition F_false (e : C) : functor C C := tpair _ (F_false_data e) (isfunctor_F_false_data e).

Definition right_unitor (e : C) : UU := F_false e ⇔ Id.

Definition unit_tensor_unit_to_unit_uniqueness {e : C} (l : left_unitor e) (r : right_unitor e) := pr1 l e = pr1 r e.

Definition triangle_identity (α : associator) (e : C) (l : left_unitor e) (r : right_unitor e) :=
  ∏ a c : C, (pr1 r a #⊗ identity c) ∘ (pr1 α ((a , e) , c)) = identity a #⊗ pr1 l c.

Local Close Scope cat.

Local Open Scope type_scope.

Definition monoidal_struct : UU :=
  ∑ α : associator, ∑ e : C, ∑ l : left_unitor e, ∑ r : right_unitor e, ∑ p : pentagon_identity α,
                                                                    triangle_identity α e l r × unit_tensor_unit_to_unit_uniqueness l r.
Local Close Scope type_scope.

End monoidal_precategory.

Definition monoidal_precat : UU := ∑ C : precategory, ∑ F : (C × C) ⟶ C, monoidal_struct C F.

Definition monoidal_precat_to_precat (M : monoidal_precat) : precategory := pr1 M.

Coercion monoidal_precat_to_precat : monoidal_precat >-> precategory.

(** A few access functions for monoidal precategories *)

Definition monoidal_precat_to_tensor (M : monoidal_precat) : (M × M) ⟶ M := pr1 (pr2 M).

Definition monoidal_precat_to_associator (M : monoidal_precat) : associator M (monoidal_precat_to_tensor M) := pr1 (pr2 (pr2 M)).

Definition monoidal_precat_to_unit (M : monoidal_precat) : ob M := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_precat_to_left_unitor (M : monoidal_precat) : left_unitor M (monoidal_precat_to_tensor M) (monoidal_precat_to_unit M)
  := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_precat_to_right_unitor (M : monoidal_precat) : right_unitor M (monoidal_precat_to_tensor M) (monoidal_precat_to_unit M)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

(** * Braided monoidal (pre)category *)

Section braided_monoidal_precategory.

Variable M : monoidal_precat.

Local Open Scope cat.

Definition braiding_on_ob : ob (M × M) -> ob (M × M).
Proof.
  intro f.
  intro x. induction x.
  - exact (f false).
  - exact (f true).
Defined.

Definition braiding_on_mor : ∏ f g : ob (M × M), f --> g -> braiding_on_ob f --> braiding_on_ob g.
Proof.
  intros f g h.
  intro x. induction x.
  - exact (h false).
  - exact (h true).
Defined.

Definition braiding_data : functor_data (M × M) (M × M) := functor_data_constr (M × M) (M × M) braiding_on_ob braiding_on_mor.

Definition braiding_idax : functor_idax braiding_data.
Proof.
  intro f.
  apply funextsec. intro x.
  induction x.
  - reflexivity.
  - reflexivity.
Defined.

Definition braiding_compax : functor_compax braiding_data.
Proof.
  intros f g h fg gh.
  apply funextsec. intro x.
  induction x.
  - reflexivity.
  - reflexivity.
Defined.

Definition isfunctor_braiding : is_functor braiding_data := dirprodpair braiding_idax braiding_compax.

Definition braiding_functor : functor (M × M) (M × M) := tpair _ braiding_data isfunctor_braiding.

Definition braiding := (monoidal_precat_to_tensor M) ⇔ functor_composite braiding_functor (monoidal_precat_to_tensor M).

Local Open Scope type_scope.

Notation "'e'" := (monoidal_precat_to_unit M).
Notation "'l'" := (monoidal_precat_to_left_unitor M).
Notation "'r'" := (monoidal_precat_to_right_unitor M).
Notation "'α'" := (monoidal_precat_to_associator M).
Notation "a ⊗ b" := (monoidal_precat_to_tensor M (a , b)) (at level 30).
Notation "f #⊗ g" := (#(monoidal_precat_to_tensor M) (f #, g)) (at level 30).

Definition braiding_unitor_identity (γ : braiding) := ∏ a : M, pr1 l a ∘ (pr1 γ (a , e)) = pr1 r a.

Definition hexagon_identity_1 (γ : braiding) :=
  ∏ a b c : M,
            (pr1 γ (c , a) #⊗ identity b) ∘ (pr1 α ((c , a) , b)) ∘ (pr1 γ (a ⊗ b , c)) =
            (pr1 α ((a , c) , b)) ∘ (identity a #⊗ pr1 γ (b , c)) ∘ (inv_from_iso (pr1 α ((a , b) , c))).

Definition hexagon_identity_2 (γ : braiding) :=
  ∏ a b c : M,
            (identity b #⊗ pr1 γ (c , a)) ∘ (inv_from_iso (pr1 α ((b , c) , a))) ∘ (pr1 γ (a , b ⊗ c)) =
            (inv_from_iso (pr1 α ((b , a) , c))) ∘ (pr1 γ (a , b) #⊗ identity c) ∘ (pr1 α ((a , b) , c)).

Definition braided_struct : UU := ∑ γ : braiding, (braiding_unitor_identity γ) × (hexagon_identity_1 γ) × (hexagon_identity_2 γ).

End braided_monoidal_precategory.

Definition braided_monoidal_precat : UU := ∑ M : monoidal_precat, braided_struct M.

(** Access functions from a braided monoidal precategory *)

Definition braided_monoidal_precat_to_braiding (M : braided_monoidal_precat) := pr1 (pr2 M).

Definition braided_monoidal_precat_to_monoidal_precat (M : braided_monoidal_precat) := pr1 M.

Coercion braided_monoidal_precat_to_monoidal_precat : braided_monoidal_precat >-> monoidal_precat.

(** * Symmetric monoidal (pre)category *)

Section symmetric_monoidal_precategory.

Variable M : braided_monoidal_precat.
Notation "a ⊗ b" := (monoidal_precat_to_tensor M (a , b)) (at level 30).
Notation "'γ'" := (braided_monoidal_precat_to_braiding M).

Definition braiding_after_braiding_is_id := ∏ a b : M, (pr1 γ (b, a)) ∘ (pr1 γ (a , b)) = identity (a ⊗ b).

End symmetric_monoidal_precategory.

Definition symmetric_monoidal_precat : UU := ∑ M : braided_monoidal_precat,  braiding_after_braiding_is_id M .

Definition symmetric_monoidal_precat_to_braided_monoidal_precat (M : symmetric_monoidal_precat) := pr1 M.

Coercion symmetric_monoidal_precat_to_braided_monoidal_precat : symmetric_monoidal_precat >-> braided_monoidal_precat.

(** * Monoidal functors *)

Section monoidal_functor.

Local Open Scope cat.

Variable M : monoidal_precat.
Variable M' : monoidal_precat.
Variable F : M ⟶ M'.

Notation "a ⊗ b" := (monoidal_precat_to_tensor M (a , b)) (at level 30).
Notation "f #⊗ g" := (#(monoidal_precat_to_tensor M) (f #, g)) (at level 30).

Notation "a ⊗' b" := (monoidal_precat_to_tensor M' (a , b)) (at level 30).
Notation "f #⊗' g":= (#(monoidal_precat_to_tensor M') (f #, g)) (at level 30).

Notation "'α'" := (monoidal_precat_to_associator M).
Notation "'α''" := (monoidal_precat_to_associator M').

Notation "'e'" := (monoidal_precat_to_unit M).
Notation "'e''" := (monoidal_precat_to_unit M').

Notation "'l'" := (monoidal_precat_to_left_unitor M).
Notation "'l''" := (monoidal_precat_to_left_unitor M').

Notation "'r'" := (monoidal_precat_to_right_unitor M).
Notation "'r''" := (monoidal_precat_to_right_unitor M').

Definition F_tensor_ob : ob (M × M) -> M'.
Proof.
  intro f.
  exact (F (f true) ⊗' F (f false)).
Defined.

Definition F_tensor_mor : ∏ f g : ob (M × M), f --> g -> F_tensor_ob f --> F_tensor_ob g.
Proof.
  intros f g h.
  exact (#F (h true) #⊗' #F (h false)).
Defined.

Definition F_tensor_data : functor_data (M × M) M' := functor_data_constr (M × M) M' F_tensor_ob F_tensor_mor.

Definition F_tensor_idax : functor_idax F_tensor_data.
Proof.
  intro f.
  unfold F_tensor_data, F_tensor_ob, F_tensor_mor. cbn.
  rewrite 2 (pr1 (pr2 F)).
  rewrite <- id_binprod_precat.
  rewrite (pr1 (pr2 (monoidal_precat_to_tensor M'))).
  reflexivity.
Defined.

Definition F_tensor_compax : functor_compax F_tensor_data.
Proof.
  intros f g h i j.
  unfold F_tensor_data, F_tensor_ob, F_tensor_mor. cbn.
  rewrite 2 (pr2 (pr2 F)).
  rewrite <- comp_binprod_precat.
  apply (pr2 (pr2 (monoidal_precat_to_tensor M'))).
Defined.

Definition isfunctor_F_tensor : is_functor F_tensor_data := dirprodpair F_tensor_idax F_tensor_compax.

Definition F_tensor : functor (M × M) M' := tpair _ F_tensor_data isfunctor_F_tensor.

Definition tensor_F_ob : ob (M × M) -> M'.
Proof.
  intro f.
  exact (F (f true ⊗ f false)).
Defined.

Definition tensor_F_mor : ∏ f g : ob (M × M), f --> g -> tensor_F_ob f --> tensor_F_ob g.
Proof.
  intros f g h.
  exact (#F (h true #⊗ h false)).
Defined.

Definition tensor_F_data : functor_data (M × M) M' := functor_data_constr (M × M) M' tensor_F_ob tensor_F_mor.

Definition tensor_F_idax : functor_idax tensor_F_data.
Proof.
  intro f.
  unfold tensor_F_data, tensor_F_ob, tensor_F_mor. cbn.
  rewrite <- id_binprod_precat.
  rewrite (pr1 (pr2 (monoidal_precat_to_tensor M))).
  apply (pr1 (pr2 F)).
Defined.

Definition tensor_F_compax : functor_compax tensor_F_data.
Proof.
  intros f g h i j.
  unfold tensor_F_data, tensor_F_ob, tensor_F_mor. cbn.
  rewrite <- comp_binprod_precat.
  rewrite (pr2 (pr2 (monoidal_precat_to_tensor M))).
  apply (pr2 (pr2 F)).
Defined.

Definition isfunctor_tensor_F : is_functor tensor_F_data := dirprodpair tensor_F_idax tensor_F_compax.

Definition tensor_F : functor (M × M) M' := tpair _ tensor_F_data isfunctor_tensor_F.

Definition hexagon_identity_3 (Φ : nat_iso F_tensor tensor_F) := ∏ a b c : M,
  #F(inv_from_iso (pr1 α ((a , b) , c))) ∘ (pr1 Φ (a ⊗ b , c)) ∘ (pr1 Φ (a , b) #⊗' identity (F c)) =
  (pr1 Φ (a , b ⊗ c)) ∘ (identity (F a) #⊗' pr1 Φ (b , c)) ∘ (inv_from_iso (pr1 α' ((F a , F b) , F c))).

Definition square_identity_1 (Φ : nat_iso F_tensor tensor_F) (φ : iso e' (F e)) :=
  ∏ a : M,  pr1 (pr1 l' (F a)) = #F(pr1 l a) ∘ (pr1 Φ (e , a)) ∘ (φ #⊗' identity (F a)).

Definition square_identity_2 (Φ : nat_iso F_tensor tensor_F) (φ : iso e' (F e)) :=
  ∏ a : M, pr1 (pr1 r' (F a)) = #F (pr1 r a) ∘ (pr1 Φ (a , e)) ∘ (identity (F a) #⊗' φ).

Local Open Scope type_scope.

Definition monoidal_functor_struct : UU := ∑ Φ : nat_iso F_tensor tensor_F, ∑ φ : iso e' (F e),
  hexagon_identity_3 Φ × square_identity_1 Φ φ × square_identity_2 Φ φ.

End monoidal_functor.

Definition monoidal_functor (M M' : monoidal_precat) : UU := ∑ F : M ⟶ M', monoidal_functor_struct M M' F.