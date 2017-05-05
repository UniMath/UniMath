(** Anthony Bordg, April-May 2017 *)

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

Lemma id_on_binprod_precat_pair_of_el {C D : precategory} (a : C) (b : D) : identity (a , b) = (identity a #, identity b).
Proof.
  apply funextsec.
  intro x. induction x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Defined.

Lemma comp_binprod_precat {C D : precategory} {u x z : C} {v y w: D} (f : u --> x) (g : v --> y) (h : x --> z) (i : y --> w) :
  (f #, g) · (h #, i) = (f · h #, g · i).
Proof.
  intros.
  apply funextsec. intro b.
  induction b.
  - cbn. reflexivity.
  - cbn. reflexivity.
Defined.

Definition binprod_precat_pair_of_is_iso_is_iso {C D : precategory} {u x : C} {v y : D} {f : u --> x} (fiso : is_iso f) {g : v --> y} (giso : is_iso g) : is_iso (f #, g).
Proof.
  apply (is_iso_qinv (f #, g) (inv_from_iso (isopair f fiso) #, inv_from_iso (isopair g giso))).
  apply dirprodpair.
  - transitivity ((isopair f fiso) · (inv_from_iso (isopair f fiso)) #, (isopair g giso) · (inv_from_iso (isopair g giso))).
    + apply comp_binprod_precat.
    + rewrite 2 iso_inv_after_iso.
      symmetry.
      apply id_on_binprod_precat_pair_of_el.
  - transitivity ((inv_from_iso (isopair f fiso)) · (isopair f fiso) #, (inv_from_iso (isopair g giso)) · (isopair g giso)).
    + apply comp_binprod_precat.
    + rewrite 2 iso_after_iso_inv.
      symmetry.
      apply id_on_binprod_precat_pair_of_el.
Defined.

Definition binprod_precat_pair_of_iso_iso {C D : precategory} {u x : C} {v y : D} (f : iso u x) (g : iso v y) : iso (u , v) (x , y) :=
  isopair (f #, g) (binprod_precat_pair_of_is_iso_is_iso (pr2 f) (pr2 g)).

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
  rewrite <- (id_on_binprod_precat_pair_of_el).
  rewrite (pr1 (pr2 F)).
  rewrite <- id_on_binprod_precat_pair_of_el.
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
  rewrite <- id_on_binprod_precat_pair_of_el.
  rewrite (pr1 (pr2 F)).
  transitivity (#F (identity ((pr1 F) (f true true, f true false) , f false))).
  - apply (maponpaths #F).
    symmetry.
    apply id_on_binprod_precat_pair_of_el.
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
  rewrite <- id_on_binprod_precat_pair_of_el.
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
  rewrite <- id_on_binprod_precat_pair_of_el.
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
  rewrite <- id_on_binprod_precat_pair_of_el.
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
  rewrite <- id_on_binprod_precat_pair_of_el.
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
  (pr1 Φ (a , b) #⊗' identity (F c)) · (pr1 Φ (a ⊗ b , c)) · #F(inv_from_iso (pr1 α ((a , b) , c))) =
  (inv_from_iso (pr1 α' ((F a , F b) , F c))) · (identity (F a) #⊗' pr1 Φ (b , c)) · (pr1 Φ (a , b ⊗ c)).

Definition square_identity_1 (Φ : nat_iso F_tensor tensor_F) (φ : iso e' (F e)) :=
  ∏ a : M,  pr1 (pr1 l' (F a)) = #F(pr1 l a) ∘ (pr1 Φ (e , a)) ∘ (φ #⊗' identity (F a)).

Definition square_identity_2 (Φ : nat_iso F_tensor tensor_F) (φ : iso e' (F e)) :=
  ∏ a : M, pr1 (pr1 r' (F a)) = #F (pr1 r a) ∘ (pr1 Φ (a , e)) ∘ (identity (F a) #⊗' φ).

Local Open Scope type_scope.

Definition monoidal_functor_struct : UU := ∑ Φ : nat_iso F_tensor tensor_F, ∑ φ : iso e' (F e),
  hexagon_identity_3 Φ × square_identity_1 Φ φ × square_identity_2 Φ φ.

End monoidal_functor.

Definition monoidal_functor (M M' : monoidal_precat) : UU := ∑ F : M ⟶ M', monoidal_functor_struct M M' F.

Definition monoidal_functor_to_functor {M M' : monoidal_precat} (F : monoidal_functor M M') : functor M M' := pr1 F.

Coercion monoidal_functor_to_functor : monoidal_functor >-> functor.

(** A few access functions from a monoidal functor *)

Definition monoidal_functor_to_nat_iso {M M' : monoidal_precat} (F : monoidal_functor M M') := pr1 (pr2 F).

Definition monoidal_functor_to_iso_unit_to_unit {M M' : monoidal_precat} (F : monoidal_functor M M') := pr1 (pr2 (pr2 F)).

Definition monoidal_functor_to_hexagon_identity {M M' : monoidal_precat} (F : monoidal_functor M M') := pr1 (pr2 (pr2 (pr2 F))).

(** * Braided monoidal functors *)

Section braided_monoidal_functor.

Variables M M': braided_monoidal_precat.
Variable F : monoidal_functor M M'.

Notation "a ⊗ b" := (monoidal_precat_to_tensor M (a , b)) (at level 30).
Notation "a ⊗' b" := (monoidal_precat_to_tensor M' (a , b)) (at level 30).

Notation "'γ'" := (braided_monoidal_precat_to_braiding M).
Notation "'γ''" := (braided_monoidal_precat_to_braiding M').

Notation "'Φ'" := (pr1 (pr2 F)).

Definition compatibility_with_braidings := ∏ a b : M, pr1 Φ (b , a) ∘ pr1 γ' (F a , F b) = #F(pr1 γ (a , b)) ∘ pr1 Φ (a , b).

End braided_monoidal_functor.

Definition braided_monoidal_functor (M M' : braided_monoidal_precat) : UU := ∑ F : monoidal_functor M M', compatibility_with_braidings M M' F.
Definition braided_monoidal_functor_to_monoidal_functor {M M' : braided_monoidal_precat} (F : braided_monoidal_functor M M') := pr1 F.

Coercion braided_monoidal_functor_to_monoidal_functor : braided_monoidal_functor >-> monoidal_functor.

(** * Symmetric monoidal functors *)

Definition symmetric_monoidal_functor (M M' : symmetric_monoidal_precat) : UU := braided_monoidal_functor M M'.

(** * Monoidal, braided monoidal, symmetric monoidal natural transformations *)

Section symmetric_nat_trans.

Variables M M' : monoidal_precat.
Variables F G : monoidal_functor M M'.
Variable α : F ⟹ G.

Notation "a ⊗ b" := (monoidal_precat_to_tensor M (a , b)) (at level 30).
Notation "a ⊗' b" := (monoidal_precat_to_tensor M' (a , b)) (at level 30).

Notation "f #⊗' g" := (#(monoidal_precat_to_tensor M') (f #, g)) (at level 30).

Notation "'e'" := (monoidal_precat_to_unit M).
Notation "'e''" := (monoidal_precat_to_unit M').

Notation "'Φ'" := (pr1 (pr2 F)).
Notation "'Γ'" := (pr1 (pr2 G)).

Notation "'φ'" := (pr1 (pr2 (pr2 F))).
Notation "'γ'" := (pr1 (pr2 (pr2 G))).

Definition square_identity_3 := ∏ a b : M, pr1 Γ (a , b) ∘ (pr1 α a #⊗' pr1 α b) = pr1 α (a ⊗ b) ∘ pr1 Φ (a , b).

Definition triangle_identity_2 := pr1 γ = pr1 α e ∘ φ.

End symmetric_nat_trans.

Local Open Scope type_scope.

Definition monoidal_nat_trans {M M' : monoidal_precat} (F G : monoidal_functor M M') : UU :=
  ∑ α : F ⟹ G, (square_identity_3 M M' F G α) × (triangle_identity_2 M M' F G α).

Definition monoidal_nat_iso {M M' : monoidal_precat} (F G : monoidal_functor M M') : UU :=
  ∑ α : nat_iso F G, (square_identity_3 M M' F G α) × (triangle_identity_2 M M' F G α).

Local Close Scope type_scope.

Definition braided_nat_trans {M M': braided_monoidal_precat} (F G : braided_monoidal_functor M M') := monoidal_nat_trans F G.

Definition braided_nat_iso {M M': braided_monoidal_precat} (F G : braided_monoidal_functor M M') := monoidal_nat_iso F G.

Definition symmetric_nat_trans {M M' : symmetric_monoidal_precat} (F G : symmetric_monoidal_functor M M') := braided_nat_trans F G.

Definition symmetric_nat_iso {M M' : symmetric_monoidal_precat} (F G : symmetric_monoidal_functor M M') := braided_nat_iso F G.

(** * The monoidal, braided monoidal, symmetric monoidal identity functor *)

Section monoidal_functor_identity.

Definition nat_iso_functor_identity (M : monoidal_precat) : (F_tensor M M Id) ⇔ (tensor_F M M Id).
Proof.
  use tpair.
  - intro x.
    exact (identity_iso (monoidal_precat_to_tensor M (x true ,  x false))).
  - intros x x' f. cbn.
    rewrite id_right.
    rewrite id_left.
    reflexivity.
Defined.

Variable M : monoidal_precat.
Notation "'e'" := (monoidal_precat_to_unit M).

Notation "'Φ'" := (nat_iso_functor_identity M).

Definition unit_iso_functor_identity : iso e (Id e) := identity_iso e.

Notation "'φ'" := (unit_iso_functor_identity).

Definition hexagon_functor_identity : hexagon_identity_3 M M Id Φ.
Proof.
  unfold hexagon_identity_3. intros a b c.
  unfold Id. cbn. rewrite <- id_on_binprod_precat_pair_of_el.
  rewrite (functor_id (monoidal_precat_to_tensor M)).
  rewrite 2 id_left.
  rewrite <- id_on_binprod_precat_pair_of_el.
  rewrite (functor_id (monoidal_precat_to_tensor M)).
  rewrite 2 id_right.
  reflexivity.
Defined.

Definition square_identity_1_functor_identity : square_identity_1 M M Id Φ φ.
Proof.
  unfold square_identity_1. intro a.
  unfold unit_iso_functor_identity. cbn.
  rewrite <- id_on_binprod_precat_pair_of_el.
  rewrite (functor_id (monoidal_precat_to_tensor M)).
  rewrite 2 id_left.
  reflexivity.
Defined.

Definition square_identity_2_functor_identity : square_identity_2 M M Id Φ φ.
Proof.
  unfold square_identity_2. intro a.
  unfold unit_iso_functor_identity. cbn.
  rewrite <- id_on_binprod_precat_pair_of_el.
  rewrite (functor_id (monoidal_precat_to_tensor M)).
  rewrite 2 id_left.
  reflexivity.
Defined.

End monoidal_functor_identity.

Definition monoidal_functor_identity (M : monoidal_precat) : monoidal_functor M M.
Proof.
  use tpair.
  - exact (functor_identity M) .
  - use tpair.
    + exact (nat_iso_functor_identity M).
    + use tpair.
      * exact (unit_iso_functor_identity M).
      *  use tpair.
         exact (hexagon_functor_identity M).
         use tpair.
         exact (square_identity_1_functor_identity M).
         exact (square_identity_2_functor_identity M).
Defined.

Section braided_monoidal_functor_identity.

Variable M : braided_monoidal_precat.

Definition compatibility_with_braidings_functor_identity : compatibility_with_braidings M M (monoidal_functor_identity M).
Proof.
  unfold compatibility_with_braidings. intros a b. cbn.
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Defined.

End braided_monoidal_functor_identity.

Definition braided_monoidal_functor_identity (M : braided_monoidal_precat) : braided_monoidal_functor M M :=
  tpair _ (monoidal_functor_identity M) (compatibility_with_braidings_functor_identity M).

Definition symmetric_monoidal_functor_identity (M : symmetric_monoidal_precat) : symmetric_monoidal_functor M M :=
  braided_monoidal_functor_identity M.

(** * Useful tools to rewrite commutative diagrams *)

Section commutative_diagrams.

Definition comm_square_with_vertical_iso {C : precategory} {x y z w : C} (f : iso x y) (g : y --> z) (i : iso w z) (h : x --> w) :
  f · g = h · i -> g · inv_from_iso i = inv_from_iso f · h.
Proof.
  intro d.
  apply (pre_comp_with_iso_is_inj C _ _ _ f (pr2 f)).
  symmetry. rewrite assoc.
  transitivity (identity x · h).
  apply cancel_postcomposition.
  apply iso_inv_after_iso.
  rewrite id_left.
  symmetry.
  apply (post_comp_with_iso_is_inj C _ _ i (pr2 i)).
  rewrite <- assoc. rewrite <- assoc. rewrite iso_after_iso_inv.
  rewrite id_right.
  exact d.
Defined.

Definition functor_on_comm_square {C D : precategory} (F : C ⟶ D) {x y z w : C} (f : x --> y) (g : y --> z) (i : w --> z) (h : x --> w) :
  f · g = h · i -> #F f · #F g = #F h · #F i.
Proof.
  intro d.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  apply maponpaths.
  exact d.
Defined.

Definition comm_square_with_bottom_horizontal_iso {C : precategory} {x y z w : C} (f : x --> y) (g : iso y z) (i : w --> z) (h : x --> w) :
  f · g = h · i -> f = h · i · inv_from_iso g.
Proof.
  intro d.
  apply (post_comp_with_iso_is_inj C _ _ g (pr2 g)).
  symmetry. rewrite <- assoc. rewrite iso_after_iso_inv.
  rewrite id_right.
  symmetry.
  exact d.
Defined.

Definition comm_hexagon_with_left_horizontal_iso {C : precategory} {u v x y z w : C} (f : u --> v) (g : v --> x) (h : x --> y) (i : z --> y)
  (j : w -->z) (k : iso u w) : f · g · h = k · j · i -> inv_from_iso k · f · g · h = j · i.
Proof.
  intro d.
  apply (pre_comp_with_iso_is_inj C _ _ _ k (pr2 k)).
  rewrite assoc. rewrite assoc. rewrite assoc. rewrite iso_inv_after_iso.
  rewrite id_left.
  symmetry. rewrite assoc. symmetry. exact d.
Defined.


End commutative_diagrams.

(** * The stability of monoidal, braided monoidal, symmetric monoidal functors by composition *)

Section monoidal_composition.

Variables M N P : monoidal_precat.
Variable F : monoidal_functor M N.
Variable G : monoidal_functor N P.

Local Open Scope cat.

Definition tensor_on_is_iso_is_iso {C : monoidal_precat} {x y z w : C} {f : x --> z} (fiso : is_iso f) {g : y --> w} (giso : is_iso g)
: is_iso (#(monoidal_precat_to_tensor C) (f #, g)).
Proof.
  apply functor_on_is_iso_is_iso.
  apply binprod_precat_pair_of_is_iso_is_iso.
  exact fiso.
  exact giso.
Defined.

Definition tensor_on_iso_iso {C : monoidal_precat} {x y z w : C} (f : iso x z) (g : iso y w) :
  iso (monoidal_precat_to_tensor C (x , y)) (monoidal_precat_to_tensor C (z , w)) :=
  isopair (#(monoidal_precat_to_tensor C) (f #, g)) (tensor_on_is_iso_is_iso (pr2 f) (pr2 g)).

Definition functor_after_tensor_on_iso_iso {C : monoidal_precat} {D : precategory} (H : C ⟶ D) {x y z w : C} (f : iso x z) (g : iso y w) :
  iso (H (monoidal_precat_to_tensor C (x , y))) (H (monoidal_precat_to_tensor C (z , w))).
Proof.
  apply functor_on_iso.
  exact (tensor_on_iso_iso f g).
Defined.

Definition tensor_after_functor_on_iso_iso {C : precategory} {D : monoidal_precat} (H : C ⟶ D) {x y z w : C} (f : iso x z) (g : iso y w) :
  iso (monoidal_precat_to_tensor D (H x , H y)) (monoidal_precat_to_tensor D (H z , H w)).
Proof.
  apply tensor_on_iso_iso.
  exact (functor_on_iso H f).
  exact (functor_on_iso H g).
Defined.

Notation "1 x" := (identity_iso x) (at level 90) : cat.


Definition family_of_iso_monoidal_functor_comp : ∏ x : ob (M × M), iso (F_tensor M P (F ∙ G) x) (tensor_F M P (F ∙ G) x).
Proof.
  intro x.
  exact (iso_comp (pr1 (monoidal_functor_to_nat_iso G) (F (x true) , F (x false))) (functor_on_iso G (pr1 (monoidal_functor_to_nat_iso F) x))).
Defined.

Lemma tensor_to_tensor_comp {x x' : ob (M × M)} (f : x --> x') : #G(#(tensor_F M N F) f) = #(tensor_F M P (F ∙ G)) f.
Proof.
  cbn. unfold tensor_F_mor.
  reflexivity.
Defined.

Lemma tensor_comp_to_tensor {x x' : ob (M × M)} (f : x --> x') : #(F_tensor M P (F ∙ G)) f =
  (pr1 (monoidal_functor_to_nat_iso G) (F (x true) , F (x false)) · #G(#(F_tensor M N F) f)) · inv_from_iso (pr1 (monoidal_functor_to_nat_iso G) (F (x' true) , F (x' false))).
Proof.
  set (d := pr2 (monoidal_functor_to_nat_iso G) (F (x true) , F (x false)) (F (x' true) , F (x' false)) (#F (f true) #, #F (f false))).
  apply (comm_square_with_bottom_horizontal_iso _ _ _ _ d).
Defined.

Definition is_nat_iso_family_of_iso_monoidal_functor_comp :
  is_nat_iso (F_tensor M P (F ∙ G)) (tensor_F M P (F ∙ G)) family_of_iso_monoidal_functor_comp.
Proof.
  intros x x' f.
  rewrite (tensor_comp_to_tensor f).
  unfold family_of_iso_monoidal_functor_comp.
  transitivity (pr1 (monoidal_functor_to_nat_iso G) (F (x true), F (x false))·
  # G (#(F_tensor M N (pr1 F)) f) · ((inv_from_iso (pr1 (monoidal_functor_to_nat_iso G) (F (x' true), F (x' false))) · pr1 (monoidal_functor_to_nat_iso G) (F (x' true), F (x' false))) · # G (pr1 (monoidal_functor_to_nat_iso F) x'))).
  - rewrite <- assoc. apply cancel_precomposition.
    rewrite <- assoc. reflexivity.
  - rewrite iso_after_iso_inv.
    rewrite id_left.
    transitivity (pr1 (monoidal_functor_to_nat_iso G) (F (x true), F (x false)) · #G (pr1 (monoidal_functor_to_nat_iso F) x) ·
                      #G (#(tensor_F M N F) f)).
    rewrite <- assoc. symmetry. rewrite <- assoc. symmetry. apply cancel_precomposition.
    apply (functor_on_comm_square G _ _ _ _ (pr2 (monoidal_functor_to_nat_iso F) x x' f)).
    reflexivity.
Defined.

Definition nat_iso_monoidal_functor_comp : F_tensor M P (functor_composite F G) ⇔ tensor_F M P (functor_composite F G) :=
  tpair _ family_of_iso_monoidal_functor_comp is_nat_iso_family_of_iso_monoidal_functor_comp.

Notation "'e'" := (monoidal_precat_to_unit M).
Notation "'e''" := (monoidal_precat_to_unit N).
Notation "'e'''" := (monoidal_precat_to_unit P).

Definition iso_unit_to_unit_monoidal_functor_comp : iso e'' ((F ∙ G) e).
Proof.
  exact (iso_comp (monoidal_functor_to_iso_unit_to_unit G) (functor_on_iso G (monoidal_functor_to_iso_unit_to_unit F))).
Defined.

Notation "'α'" := (monoidal_precat_to_associator M).
Notation "'α''" := (monoidal_precat_to_associator N).
Notation "a ⊗ b" := (monoidal_precat_to_tensor M (a , b)) (at level 30).
Notation "f #⊗ g" := (#(monoidal_precat_to_tensor M) (f #, g)) (at level 30).
Notation "a ⊗' b" := (monoidal_precat_to_tensor N (a , b)) (at level 30).
Notation "f #⊗' g" := (#(monoidal_precat_to_tensor N) (f #, g)) (at level 30).
Notation "'Φ'" := (monoidal_functor_to_nat_iso F).

Lemma image_of_hexagon_identity : ∏ a b c : M,
  #G((pr1 Φ (a , b)) #⊗' identity (F c)) · #G(pr1 Φ (a ⊗ b , c)) · #G(#F(inv_from_iso (pr1 α ((a , b) , c)))) =
  #G(inv_from_iso (pr1 α' ((F a , F b) , F c))) · #G(identity (F a) #⊗' (pr1 Φ (b , c))) · #G(pr1 Φ (a , b ⊗ c)).
Proof.
  intros a b c.
  rewrite <- 4 (functor_comp G).
  apply maponpaths.
  apply (monoidal_functor_to_hexagon_identity F).
Defined.

Lemma image_of_hexagon_identity_bis : ∏ a b c : M,
  #G(pr1 Φ (a ⊗ b , c)) · #G(#F(inv_from_iso (pr1 α ((a , b) , c)))) =
  inv_from_iso (functor_after_tensor_on_iso_iso G (pr1 Φ (a , b)) (1 (F c))) · #G(inv_from_iso (pr1 α' ((F a , F b) , F c))) · #G(identity (F a) #⊗' (pr1 Φ (b , c))) · #G(pr1 Φ (a , b ⊗ c)).
Proof.
  intros a b c.
  symmetry.
  rewrite <- assoc. rewrite <- assoc.
  apply iso_inv_on_right.
  symmetry.
  cbn. rewrite assoc. rewrite assoc. apply image_of_hexagon_identity.
Defined.

(* Definition hexagon_identity_monoidal_functor_comp : hexagon_identity_3 M P (functor_composite F G) (nat_iso_monoidal_functor_comp).
Proof.
  intros a b c.
  unfold nat_iso_monoidal_functor_comp. cbn.
  rewrite <- assoc. rewrite <- assoc. rewrite assoc.
  (* rewrite <- (id_left (identity ((F ∙ G) c))).
  rewrite <- (comp_binprod_precat).*)
  transitivity (# (monoidal_precat_to_tensor P) (pr1 (monoidal_functor_to_nat_iso G) (F a, F b) · # G (pr1 Φ (a, b)) #, identity (G (F c))) · pr1 (monoidal_functor_to_nat_iso G) (F (a ⊗ b), F c) · (inv_from_iso (isopair (#G((pr1 Φ (a , b)) #⊗' identity (F c))) is_iso_G_after_tensor_on_iso) · #G(inv_from_iso (pr1 α' ((F a , F b) , F c))) · #G(identity (F a) #⊗' (pr1 Φ (b , c))) · #G(pr1 Φ (a , b ⊗ c)))).
  - apply cancel_precomposition. apply image_of_hexagon_identity_bis.
  - transitivity (((# (monoidal_precat_to_tensor P) (pr1 (monoidal_functor_to_nat_iso G) (F a, F b) · # G (pr1 Φ (a, b)) #, identity (G (F c))) · pr1 (monoidal_functor_to_nat_iso G) (F (a ⊗ b), F c))
   · inv_from_iso
     (isopair
        (# G
           (# (monoidal_precat_to_tensor N) (pr1 Φ (a, b) #, identity (F c))))
        is_iso_G_after_tensor_on_iso))
   · (# G (inv_from_iso (pr1 α' ((F a, F b), F c)))
   · # G (# (monoidal_precat_to_tensor N) (identity (F a) #, pr1 Φ (b, c)))
   · # G (pr1 Φ (a, b ⊗ c)))).
    rewrite assoc4.
    + *)




End monoidal_composition.