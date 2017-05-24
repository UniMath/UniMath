(** Anthony Bordg, April-May 2017 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.sub_precategories.


Notation "1 x" := (identity_iso x) (at level 90) : cat.

Definition Id {C : precategory} := functor_identity C.

(** * Monoidal category *)


Definition binprod_cat (C D : precategory) : precategory.
Proof.
  refine (product_precategory bool _).
  intro x. induction x.
  - exact C.
  - exact D.
Defined.

Notation "C × D" := (binprod_cat C D) : cat.

Local Open Scope cat.

Definition binprod_cat_pair_of_el {C D : precategory} (a : C) (b : D) : ob (C × D).
Proof.
  intro x. induction x.
  - exact a.
  - exact b.
Defined.

Notation "( a , b )" := (binprod_cat_pair_of_el a b) (right associativity) : cat.

Definition binprod_cat_pair_of_mor {C D : precategory} {a c : C} {b d : D} (f : a --> c) (g : b --> d) : (a , b) --> (c , d).
Proof.
  intro x. induction x.
  - exact f.
  - exact g.
Defined.

Notation "( f #, g )" := (binprod_cat_pair_of_mor f g) (right associativity) : cat.

Lemma id_on_binprod_cat_pair_of_el {C D : precategory} (a : C) (b : D) : identity (a , b) = (identity a #, identity b).
Proof.
  apply funextsec.
  intro x. induction x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Defined.

Lemma binprod_cat_comp {C D : precategory} {u x z : C} {v y w: D} (f : u --> x) (g : v --> y) (h : x --> z) (i : y --> w) :
  (f #, g) · (h #, i) = (f · h #, g · i).
Proof.
  intros.
  apply funextsec. intro b.
  induction b.
  - cbn. reflexivity.
  - cbn. reflexivity.
Defined.

Definition is_iso_binprod_cat_pair_of_is_iso {C D : precategory} {u x : C} {v y : D} {f : u --> x} (fiso : is_iso f) {g : v --> y}
  (giso : is_iso g) : is_iso (f #, g).
Proof.
  apply (is_iso_qinv (f #, g) (inv_from_iso (isopair f fiso) #, inv_from_iso (isopair g giso))).
  apply dirprodpair.
  - transitivity ((isopair f fiso) · (inv_from_iso (isopair f fiso)) #, (isopair g giso) · (inv_from_iso (isopair g giso))).
    + apply binprod_cat_comp.
    + rewrite 2 iso_inv_after_iso.
      symmetry.
      apply id_on_binprod_cat_pair_of_el.
  - transitivity ((inv_from_iso (isopair f fiso)) · (isopair f fiso) #, (inv_from_iso (isopair g giso)) · (isopair g giso)).
    + apply binprod_cat_comp.
    + rewrite 2 iso_after_iso_inv.
      symmetry.
      apply id_on_binprod_cat_pair_of_el.
Defined.

Definition iso_binprod_cat_pair_of_iso {C D : precategory} {u x : C} {v y : D} (f : iso u x) (g : iso v y) : iso (u , v) (x , y) :=
  isopair (f #, g) (is_iso_binprod_cat_pair_of_is_iso (pr2 f) (pr2 g)).

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


Section monoidal_category.

Variable C : precategory.
Variable F : (C × C) ⟶ C.
Variable e : C.

Notation "a ⊗ b" := (F (a , b)) (at level 31, left associativity) : cat.
(** use \ox with Agda input mode *)

Notation "f #⊗ g" := (#F (f #, g)) (at level 31, left associativity) : cat.

Definition dom_associator_on_ob : ob ((C × C) × C) -> ob C.
Proof.
 intro f.
 exact ((f true true ⊗ f true false) ⊗ f false).
Defined.

Definition dom_associator_on_mor : ∏  f g : ob ((C × C) × C), f --> g -> dom_associator_on_ob f --> dom_associator_on_ob g.
Proof.
  intros f g h.
  exact ((h true true #⊗ h true false) #⊗ h false).
Defined.

Definition dom_associator_data : functor_data ((C × C) × C) C :=
  functor_data_constr ((C × C) × C) C dom_associator_on_ob dom_associator_on_mor.

Definition dom_associator_idax : functor_idax dom_associator_data.
Proof.
  intro f.
  unfold dom_associator_data, dom_associator_on_ob, dom_associator_on_mor. cbn.
  rewrite <- id_on_binprod_cat_pair_of_el.
  rewrite (functor_id F).
  transitivity (#F (identity ((pr1 F) (f true true, f true false) , f false))).
  - apply (maponpaths #F).
    symmetry.
    apply id_on_binprod_cat_pair_of_el.
  - apply (functor_id F).
Defined.

Definition dom_associator_compax : functor_compax dom_associator_data.
Proof.
  intros a b c f g.
  unfold dom_associator_data, functor_data_constr, dom_associator_on_mor. cbn.
  rewrite <- (binprod_cat_comp ).
  transitivity (#F ((#F (f true true #, f true false)  #, f false) · (#F (g true true #, g true false) #, g false))).
  - rewrite (functor_comp F).
    rewrite <- (binprod_cat_comp).
    reflexivity.
  - apply (functor_comp F).
Defined.

Definition is_functor_dom_associator_data : is_functor dom_associator_data := dirprodpair dom_associator_idax dom_associator_compax.

Definition dom_associator : functor ((C × C) × C) C := tpair _ dom_associator_data is_functor_dom_associator_data.

Definition cod_associator_on_ob : ob ((C × C) × C) -> ob C.
Proof.
 intro f.
 exact (f true true ⊗ (f true false ⊗ f false)).
Defined.

Definition cod_associator_on_mor : ∏  f g : ob ((C × C) × C), f --> g -> cod_associator_on_ob f --> cod_associator_on_ob g.
Proof.
  intros f g h.
  exact (h true true #⊗ (h true false #⊗ h false)).
Defined.

Definition cod_associator_data : functor_data ((C × C) × C) C :=
  functor_data_constr ((C × C) × C) C cod_associator_on_ob cod_associator_on_mor.

Definition cod_associator_idax : functor_idax cod_associator_data.
Proof.
  intro f.
  unfold cod_associator_data, cod_associator_on_ob, cod_associator_on_mor. cbn.
  rewrite <- (id_on_binprod_cat_pair_of_el).
  rewrite (functor_id F).
  rewrite <- id_on_binprod_cat_pair_of_el.
  apply (functor_id F).
Defined.

Definition cod_associator_compax : functor_compax cod_associator_data.
Proof.
  intros a b c f g.
  unfold cod_associator_data, functor_data_constr, cod_associator_on_mor. cbn.
  rewrite <- (binprod_cat_comp).
  rewrite (functor_comp F).
  rewrite <- (binprod_cat_comp).
  apply (functor_comp F).
Defined.

Definition is_functor_cod_associator_data : is_functor cod_associator_data := dirprodpair cod_associator_idax cod_associator_compax.

Definition cod_associator : functor ((C × C) × C) C := tpair _ cod_associator_data is_functor_cod_associator_data.

Definition associator : UU := nat_iso dom_associator cod_associator.

Definition pentagon_eq (α : associator) := ∏ a b c d : C,
  pr1 α ((a , b) , c) #⊗ (1 d) · pr1 α ((a , b ⊗ c) , d) · (1 a) #⊗ pr1 α ((b , c) , d) = pr1 α ((a ⊗ b , c) , d) · pr1 α ((a , b) , c ⊗ d).

Definition dom_left_unitor_on_ob : ob C -> ob C.
Proof.
  intro c.
  exact (e ⊗ c).
Defined.

Definition dom_left_unitor_on_mor : ∏  c d : ob C, c --> d -> dom_left_unitor_on_ob c --> dom_left_unitor_on_ob d.
Proof.
  intros c d f.
  exact ((1 e) #⊗ f).
Defined.

Definition dom_left_unitor_data : functor_data C C := functor_data_constr C C dom_left_unitor_on_ob dom_left_unitor_on_mor.

Definition dom_left_unitor_idax : functor_idax dom_left_unitor_data.
Proof.
  intro c.
  unfold dom_left_unitor_data, dom_left_unitor_on_ob, dom_left_unitor_on_mor. cbn.
  rewrite <- id_on_binprod_cat_pair_of_el.
  apply (functor_id F).
Defined.

Definition dom_left_unitor_compax : functor_compax dom_left_unitor_data.
Proof.
  intros a b c f g.
  unfold dom_left_unitor_data, dom_left_unitor_on_ob, dom_left_unitor_on_mor. cbn.
  rewrite <- (functor_comp F).
  apply maponpaths.
  symmetry.
  rewrite binprod_cat_comp.
  rewrite (id_left).
  reflexivity.
Defined.

Definition is_functor_dom_left_unitor_data : is_functor dom_left_unitor_data := dirprodpair dom_left_unitor_idax dom_left_unitor_compax.

Definition dom_left_unitor : functor C C := tpair _ dom_left_unitor_data is_functor_dom_left_unitor_data.

Definition left_unitor : UU := dom_left_unitor ⇔ Id.

Definition dom_right_unitor_on_ob : ob C -> ob C.
Proof.
  intro c.
  exact (c ⊗ e).
Defined.

Definition dom_right_unitor_on_mor : ∏  c d : ob C, c --> d -> dom_right_unitor_on_ob c --> dom_right_unitor_on_ob d.
Proof.
  intros c d f.
  exact (f #⊗ (1 e)).
Defined.

Definition dom_right_unitor_data : functor_data C C := functor_data_constr C C dom_right_unitor_on_ob dom_right_unitor_on_mor.

Definition dom_right_unitor_idax : functor_idax dom_right_unitor_data.
Proof.
  intro c.
  unfold dom_right_unitor_data, dom_right_unitor_on_ob, dom_right_unitor_on_mor. cbn.
  rewrite <- id_on_binprod_cat_pair_of_el.
  apply (functor_id F).
Defined.

Definition dom_right_unitor_compax : functor_compax dom_right_unitor_data.
Proof.
  intros a b c f g.
  unfold dom_right_unitor_data, dom_right_unitor_on_ob, dom_right_unitor_on_mor. cbn.
  rewrite <- (functor_comp F).
  apply maponpaths.
  symmetry.
  rewrite binprod_cat_comp.
  rewrite (id_left).
  reflexivity.
Defined.

Definition is_functor_dom_right_unitor_data : is_functor dom_right_unitor_data := dirprodpair dom_right_unitor_idax dom_right_unitor_compax.

Definition dom_right_unitor : functor C C := tpair _ dom_right_unitor_data is_functor_dom_right_unitor_data.

Definition right_unitor : UU := dom_right_unitor ⇔ Id.

Definition triangle_eq (α : associator) (l : left_unitor) (r : right_unitor) :=
  ∏ a b : C, (pr1 r a #⊗ (1 b)) =  pr1 α ((a , e) , b) ·  (1 a) #⊗ pr1 l b.

Local Close Scope cat.

Local Open Scope type_scope.

Definition monoidal_struct : UU :=
  ∑ α : associator, ∑ l : left_unitor, ∑ r : right_unitor, pentagon_eq α × triangle_eq α l r.

Local Close Scope type_scope.

End monoidal_category.

Definition monoidal_cat : UU := ∑ C : precategory, ∑ F : (C × C) ⟶ C, ∑ unit : C, monoidal_struct C F unit.

Definition monoidal_cat_to_cat (M : monoidal_cat) : precategory := pr1 M.

Coercion monoidal_cat_to_cat : monoidal_cat >-> precategory.

(** A few access functions for monoidal categories *)

Definition monoidal_cat_to_tensor (M : monoidal_cat) : (M × M) ⟶ M := pr1 (pr2 M).

Definition monoidal_cat_to_unit (M : monoidal_cat) : M := pr1 (pr2 (pr2 M)).

Definition monoidal_cat_to_associator (M : monoidal_cat) : associator M (monoidal_cat_to_tensor M) := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_cat_to_left_unitor (M : monoidal_cat) : left_unitor M (monoidal_cat_to_tensor M) (monoidal_cat_to_unit M)
  := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_cat_to_right_unitor (M : monoidal_cat) : right_unitor M (monoidal_cat_to_tensor M) (monoidal_cat_to_unit M)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

(** * Braided monoidal category *)

Section braided_monoidal_category.

Variable M : monoidal_cat.

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

Definition is_functor_braiding : is_functor braiding_data := dirprodpair braiding_idax braiding_compax.

Definition braiding_functor : functor (M × M) (M × M) := tpair _ braiding_data is_functor_braiding.

Definition braiding := (monoidal_cat_to_tensor M) ⇔ functor_composite braiding_functor (monoidal_cat_to_tensor M).

Local Open Scope type_scope.

Notation "'e'" := (monoidal_cat_to_unit M).
Notation "'l'" := (monoidal_cat_to_left_unitor M).
Notation "'r'" := (monoidal_cat_to_right_unitor M).
Notation "'α'" := (monoidal_cat_to_associator M).
Notation "a ⊗ b" := (monoidal_cat_to_tensor M (a , b)) (at level 31).
Notation "f #⊗ g" := (#(monoidal_cat_to_tensor M) (f #, g)) (at level 31).

Definition hexagon_eq_1 (γ : braiding) := ∏ a b c : M,
  pr1 γ (a , b ⊗ c) · (pr1 α ((b , c) , a) · (1 b) #⊗ pr1 γ (c , a)) =
  inv_from_iso (pr1 α ((a , b) , c)) · pr1 γ (a , b) #⊗ (1 c) · pr1 α ((b , a) , c).

Definition hexagon_eq_2 (γ : braiding) := ∏ a b c : M,
  pr1 γ ((a ⊗ b) , c) · (inv_from_iso (pr1 α ((c , a) , b)) · pr1 γ (c , a) #⊗ (1 b)) =
  pr1 α ((a , b) , c) · (1 a) #⊗ pr1 γ (b , c) · inv_from_iso (pr1 α ((a , c) , b)).

Definition braided_struct : UU := ∑ γ : braiding, (hexagon_eq_1 γ) × (hexagon_eq_2 γ).

End braided_monoidal_category.

Definition braided_monoidal_cat : UU := ∑ M : monoidal_cat, braided_struct M.

(** Access functions from a braided monoidal category *)

Definition braided_monoidal_cat_to_braiding (M : braided_monoidal_cat) := pr1 (pr2 M).

Definition braided_monoidal_cat_to_monoidal_cat (M : braided_monoidal_cat) := pr1 M.

Coercion braided_monoidal_cat_to_monoidal_cat : braided_monoidal_cat >-> monoidal_cat.

(** * Symmetric monoidal category *)

Section symmetric_monoidal_category.

Variable M : braided_monoidal_cat.
Notation "a ⊗ b" := (monoidal_cat_to_tensor M (a , b)) (at level 31).
Notation "'γ'" := (braided_monoidal_cat_to_braiding M).

Definition braiding_after_braiding_eq := ∏ a b : M, pr1 γ (a , b) · pr1 γ (b , a) = identity (a ⊗ b).

End symmetric_monoidal_category.

Definition symmetric_monoidal_cat : UU := ∑ M : braided_monoidal_cat,  braiding_after_braiding_eq M .

Definition symmetric_monoidal_cat_to_braided_monoidal_cat (M : symmetric_monoidal_cat) := pr1 M.

Coercion symmetric_monoidal_cat_to_braided_monoidal_cat : symmetric_monoidal_cat >-> braided_monoidal_cat.

(** * Monoidal functors *)

Section monoidal_functor.

Local Open Scope cat.

Variable M : monoidal_cat.
Variable M' : monoidal_cat.
Variable F : M ⟶ M'.

Notation "a ⊗ b" := (monoidal_cat_to_tensor M (a , b)) (at level 31).
Notation "f #⊗ g" := (#(monoidal_cat_to_tensor M) (f #, g)) (at level 31).

Notation "a ⊗' b" := (monoidal_cat_to_tensor M' (a , b)) (at level 31).
Notation "f #⊗' g":= (#(monoidal_cat_to_tensor M') (f #, g)) (at level 31).

Notation "'α'" := (monoidal_cat_to_associator M).
Notation "'α''" := (monoidal_cat_to_associator M').

Notation "'e'" := (monoidal_cat_to_unit M).
Notation "'e''" := (monoidal_cat_to_unit M').

Notation "'l'" := (monoidal_cat_to_left_unitor M).
Notation "'l''" := (monoidal_cat_to_left_unitor M').

Notation "'r'" := (monoidal_cat_to_right_unitor M).
Notation "'r''" := (monoidal_cat_to_right_unitor M').

Definition tensor_after_functor_ob : ob (M × M) -> M'.
Proof.
  intro f.
  exact (F (f true) ⊗' F (f false)).
Defined.

Definition tensor_after_functor_mor : ∏ f g : ob (M × M),
  f --> g -> tensor_after_functor_ob f --> tensor_after_functor_ob g.
Proof.
  intros f g h.
  exact (#F (h true) #⊗' #F (h false)).
Defined.

Definition tensor_after_functor_data : functor_data (M × M) M' :=
  functor_data_constr (M × M) M' tensor_after_functor_ob tensor_after_functor_mor.

Definition tensor_after_functor_idax : functor_idax tensor_after_functor_data.
Proof.
  intro f.
  unfold tensor_after_functor_data, tensor_after_functor_ob, tensor_after_functor_mor. cbn.
  rewrite 2 (functor_id F).
  rewrite <- id_on_binprod_cat_pair_of_el.
  rewrite (functor_id (monoidal_cat_to_tensor M')).
  reflexivity.
Defined.

Definition tensor_after_functor_compax : functor_compax tensor_after_functor_data.
Proof.
  intros f g h i j.
  unfold tensor_after_functor_data, tensor_after_functor_ob, tensor_after_functor_mor. cbn.
  rewrite 2 (functor_comp F).
  rewrite <- binprod_cat_comp.
  apply (functor_comp (monoidal_cat_to_tensor M')).
Defined.

Definition is_functor_tensor_after_functor : is_functor tensor_after_functor_data :=
  dirprodpair tensor_after_functor_idax tensor_after_functor_compax.

Definition tensor_after_functor : functor (M × M) M' := tpair _ tensor_after_functor_data is_functor_tensor_after_functor.

Definition functor_after_tensor_ob : ob (M × M) -> M'.
Proof.
  intro f.
  exact (F (f true ⊗ f false)).
Defined.

Definition functor_after_tensor_mor : ∏ f g : ob (M × M), f --> g -> functor_after_tensor_ob f --> functor_after_tensor_ob g.
Proof.
  intros f g h.
  exact (#F (h true #⊗ h false)).
Defined.

Definition functor_after_tensor_data : functor_data (M × M) M' :=
  functor_data_constr (M × M) M' functor_after_tensor_ob functor_after_tensor_mor.

Definition functor_after_tensor_idax : functor_idax functor_after_tensor_data.
Proof.
  intro f.
  unfold functor_after_tensor_data, functor_after_tensor_ob, functor_after_tensor_mor. cbn.
  rewrite <- id_on_binprod_cat_pair_of_el.
  rewrite (functor_id (monoidal_cat_to_tensor M)).
  apply (functor_id F).
Defined.

Definition functor_after_tensor_compax : functor_compax functor_after_tensor_data.
Proof.
  intros f g h i j.
  unfold functor_after_tensor_data, functor_after_tensor_ob, functor_after_tensor_mor. cbn.
  rewrite <- binprod_cat_comp.
  rewrite (functor_comp (monoidal_cat_to_tensor M)).
  apply (functor_comp F).
Defined.

Definition is_functor_functor_after_tensor : is_functor functor_after_tensor_data :=
  dirprodpair functor_after_tensor_idax functor_after_tensor_compax.

Definition functor_after_tensor : functor (M × M) M' := tpair _ functor_after_tensor_data is_functor_functor_after_tensor.

Definition hexagon_eq_3 (Φ : nat_iso tensor_after_functor functor_after_tensor) := ∏ a b c : M,
  pr1 α' ((F a , F b) , F c) · (identity (F a) #⊗' pr1 Φ (b , c) · pr1 Φ (a , b ⊗ c)) =
  pr1 Φ (a , b) #⊗' identity (F c) · pr1 Φ (a ⊗ b , c) · #F(pr1 α ((a , b) , c)).

Definition square_eq_1 (Φ : nat_iso tensor_after_functor functor_after_tensor) (φ : iso e' (F e)) :=
  ∏ a : M, φ #⊗' identity (F a) · pr1 Φ (e , a) · #F(pr1 l a) = pr1 l' (F a).

Definition square_eq_2 (Φ : nat_iso tensor_after_functor functor_after_tensor) (φ : iso e' (F e)) :=
  ∏ a : M, identity (F a) #⊗' φ · pr1 Φ (a , e) · #F(pr1 r a) = pr1 r' (F a).

Local Open Scope type_scope.

Definition monoidal_functor_struct : UU :=
  ∑ Φ : nat_iso tensor_after_functor functor_after_tensor, ∑ φ : iso e' (F e), hexagon_eq_3 Φ × square_eq_1 Φ φ × square_eq_2 Φ φ.

End monoidal_functor.

Definition monoidal_functor (M M' : monoidal_cat) : UU := ∑ F : M ⟶ M', monoidal_functor_struct M M' F.

Definition monoidal_functor_to_functor {M M' : monoidal_cat} (F : monoidal_functor M M') : functor M M' := pr1 F.

Coercion monoidal_functor_to_functor : monoidal_functor >-> functor.

(** A few access functions from a monoidal functor *)

Definition monoidal_functor_to_nat_iso {M M' : monoidal_cat} (F : monoidal_functor M M') := pr1 (pr2 F).

Definition monoidal_functor_to_iso_unit_to_unit {M M' : monoidal_cat} (F : monoidal_functor M M') := pr1 (pr2 (pr2 F)).

Definition monoidal_functor_to_hexagon_eq {M M' : monoidal_cat} (F : monoidal_functor M M') := pr1 (pr2 (pr2 (pr2 F))).

Definition monoidal_functor_to_square_eq_1 {M M' : monoidal_cat} (F : monoidal_functor M M') := pr1 (pr2 (pr2 (pr2 (pr2 F)))).

Definition monoidal_functor_to_square_eq_2 {M M' : monoidal_cat} (F : monoidal_functor M M') := pr2 (pr2 (pr2 (pr2 (pr2 F)))).

(** * Braided monoidal functors *)

Section braided_monoidal_functor.

Variables M M': braided_monoidal_cat.
Variable F : monoidal_functor M M'.

Notation "a ⊗ b" := (monoidal_cat_to_tensor M (a , b)) (at level 31).
Notation "a ⊗' b" := (monoidal_cat_to_tensor M' (a , b)) (at level 31).

Notation "'γ'" := (braided_monoidal_cat_to_braiding M).
Notation "'γ''" := (braided_monoidal_cat_to_braiding M').

Notation "'Φ'" := (monoidal_functor_to_nat_iso F).

Definition compatibility_with_braidings := ∏ a b : M, pr1 Φ (a , b) · #F(pr1 γ (a , b)) = pr1 γ' (F a , F b) · pr1 Φ (b , a).

End braided_monoidal_functor.

Definition braided_monoidal_functor (M M' : braided_monoidal_cat) : UU := ∑ F : monoidal_functor M M', compatibility_with_braidings M M' F.

(** Two access functions from braided monoidal functors *)

Definition braided_monoidal_functor_to_monoidal_functor {M M' : braided_monoidal_cat} (F : braided_monoidal_functor M M') := pr1 F.

Definition braided_monoidal_functor_to_compatibility_with_braidings {M M' : braided_monoidal_cat} (F : braided_monoidal_functor M M') := pr2 F.

Coercion braided_monoidal_functor_to_monoidal_functor : braided_monoidal_functor >-> monoidal_functor.

(** * Symmetric monoidal functors *)

Definition symmetric_monoidal_functor (M M' : symmetric_monoidal_cat) : UU := braided_monoidal_functor M M'.

(** * Monoidal, braided monoidal, symmetric monoidal natural transformations *)

Section symmetric_nat_trans.

Variables M M' : monoidal_cat.
Variables F G : monoidal_functor M M'.
Variable α : F ⟹ G.

Notation "a ⊗ b" := (monoidal_cat_to_tensor M (a , b)) (at level 31).
Notation "a ⊗' b" := (monoidal_cat_to_tensor M' (a , b)) (at level 31).

Notation "f #⊗' g" := (#(monoidal_cat_to_tensor M') (f #, g)) (at level 31).

Notation "'e'" := (monoidal_cat_to_unit M).
Notation "'e''" := (monoidal_cat_to_unit M').

Notation "'Φ'" := (monoidal_functor_to_nat_iso F).
Notation "'Γ'" := (monoidal_functor_to_nat_iso G).

Notation "'φ'" := (monoidal_functor_to_iso_unit_to_unit F).
Notation "'γ'" := (monoidal_functor_to_iso_unit_to_unit G).

Definition square_eq_3 := ∏ a b : M, pr1 Φ (a , b) · pr1 α (a ⊗ b) = (pr1 α a #⊗' pr1 α b) · pr1 Γ (a , b).

Definition triangle_eq_2 :=  φ · pr1 α e = γ.

End symmetric_nat_trans.

Local Open Scope type_scope.

Definition monoidal_nat_trans {M M' : monoidal_cat} (F G : monoidal_functor M M') : UU :=
  ∑ α : F ⟹ G, (square_eq_3 M M' F G α) × (triangle_eq_2 M M' F G α).

Definition monoidal_nat_iso {M M' : monoidal_cat} (F G : monoidal_functor M M') : UU :=
  ∑ α : nat_iso F G, (square_eq_3 M M' F G α) × (triangle_eq_2 M M' F G α).

Local Close Scope type_scope.

Definition braided_monoidal_nat_trans {M M': braided_monoidal_cat} (F G : braided_monoidal_functor M M') := monoidal_nat_trans F G.

Definition braided_monoidal_nat_iso {M M': braided_monoidal_cat} (F G : braided_monoidal_functor M M') := monoidal_nat_iso F G.

Definition symmetric_monoidal_nat_trans {M M' : symmetric_monoidal_cat} (F G : symmetric_monoidal_functor M M') :=
  braided_monoidal_nat_trans F G.

Definition symmetric_monoidal_nat_iso {M M' : symmetric_monoidal_cat} (F G : symmetric_monoidal_functor M M') :=
  braided_monoidal_nat_iso F G.

(** * The monoidal, braided monoidal, symmetric monoidal identity functor *)

Section monoidal_functor_identity.

Definition nat_iso_functor_identity (M : monoidal_cat) : (tensor_after_functor M M Id) ⇔ (functor_after_tensor M M Id).
Proof.
  use tpair.
  - intro x.
    exact (identity_iso (monoidal_cat_to_tensor M (x true ,  x false))).
  - intros x x' f. cbn.
    rewrite id_right.
    rewrite id_left.
    reflexivity.
Defined.

Variable M : monoidal_cat.
Notation "'e'" := (monoidal_cat_to_unit M).

Notation "'Φ'" := (nat_iso_functor_identity M).

Definition unit_iso_functor_identity : iso e (Id e) := identity_iso e.

Notation "'φ'" := (unit_iso_functor_identity).

Definition hexagon_functor_identity : hexagon_eq_3 M M Id Φ.
Proof.
  unfold hexagon_eq_3. intros a b c.
  unfold Id. cbn. rewrite <- id_on_binprod_cat_pair_of_el.
  rewrite (functor_id (monoidal_cat_to_tensor M)).
  rewrite 2 id_right.
  rewrite <- id_on_binprod_cat_pair_of_el.
  rewrite (functor_id (monoidal_cat_to_tensor M)).
  rewrite 2 id_left.
  reflexivity.
Defined.

Definition square_eq_1_functor_identity : square_eq_1 M M Id Φ φ.
Proof.
  unfold square_eq_1. intro a.
  unfold unit_iso_functor_identity. cbn.
  rewrite <- id_on_binprod_cat_pair_of_el.
  rewrite (functor_id (monoidal_cat_to_tensor M)).
  rewrite 2 id_left.
  reflexivity.
Defined.

Definition square_eq_2_functor_identity : square_eq_2 M M Id Φ φ.
Proof.
  unfold square_eq_2. intro a.
  unfold unit_iso_functor_identity. cbn.
  rewrite <- id_on_binprod_cat_pair_of_el.
  rewrite (functor_id (monoidal_cat_to_tensor M)).
  rewrite 2 id_left.
  reflexivity.
Defined.

End monoidal_functor_identity.

Definition monoidal_functor_identity (M : monoidal_cat) : monoidal_functor M M.
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
         exact (square_eq_1_functor_identity M).
         exact (square_eq_2_functor_identity M).
Defined.

Section braided_monoidal_functor_identity.

Variable M : braided_monoidal_cat.

Definition compatibility_with_braidings_functor_identity : compatibility_with_braidings M M (monoidal_functor_identity M).
Proof.
  unfold compatibility_with_braidings. intros a b. cbn.
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Defined.

End braided_monoidal_functor_identity.

Definition braided_monoidal_functor_identity (M : braided_monoidal_cat) : braided_monoidal_functor M M :=
  tpair _ (monoidal_functor_identity M) (compatibility_with_braidings_functor_identity M).

Definition symmetric_monoidal_functor_identity (M : symmetric_monoidal_cat) : symmetric_monoidal_functor M M :=
  braided_monoidal_functor_identity M.

(** * Useful tools to rewrite commutative diagrams *)

Section commutative_diagrams.

Definition comm_square_to_rotated_comm_square_by_90 {C : precategory} {x y z w : C} (f : iso x y) (g : y --> z) (i : iso w z) (h : x --> w) :
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
  rewrite <- 2 functor_comp.
  apply maponpaths.
  exact d.
Defined.

Definition functor_on_comm_square_with_reverse_vertical_arrows {C D : precategory} (F : C ⟶ D) {x y z w : C} (f : x --> y) (g : y --> z)
  (i : z --> w) (h : x --> w) : f · g · i = h -> #F f · #F g · #F i = #F h.
Proof.
  intro d.
  rewrite <- 2 (functor_comp F).
  apply maponpaths.
  exact d.
Defined.

Definition comm_square_to_left_vertical_arrow {C : precategory} {x y z w : C} (f : x --> y) (g : iso y z) (i : w --> z) (h : x --> w) :
  f · g = h · i -> f = h · i · inv_from_iso g.
Proof.
  intro d.
  apply (post_comp_with_iso_is_inj C _ _ g (pr2 g)).
  symmetry. rewrite <- assoc. rewrite iso_after_iso_inv.
  rewrite id_right.
  symmetry.
  exact d.
Defined.

Definition comm_square_to_upper_horizontal_arrow {C : precategory} {x y z w : C} (f : x --> y) (g : y --> z) (i : w --> z) (iiso : is_iso i)
   (h : x --> w) : f · g = h · i -> h = f · g · inv_from_iso (isopair i iiso).
Proof.
  intro d.
  apply (post_comp_with_iso_is_inj C _ _ i iiso).
  rewrite <- assoc. rewrite iso_after_iso_inv.
  rewrite id_right.
  symmetry. exact d.
Defined.

Definition comm_hexagon_to_comm_hexagon_with_inverse_left_horizontal_iso {C : precategory} {u v x y z w : C} (f : u --> v) (g : v --> x)
  (h : x --> y) (i : z --> y) (j : w -->z) (k : iso u w) : f · (g · h) = k · j · i -> inv_from_iso k · (f · (g · h)) = j · i.
Proof.
  intro d.
  apply (pre_comp_with_iso_is_inj C _ _ _ k (pr2 k)).
  rewrite assoc. rewrite iso_inv_after_iso.
  rewrite id_left.
  symmetry. rewrite assoc. symmetry. exact d.
Defined.


End commutative_diagrams.

(** * The stability of monoidal, braided monoidal, symmetric monoidal functors by composition *)

Section monoidal_composition.

Variables M N P : monoidal_cat.
Variable F : monoidal_functor M N.
Variable G : monoidal_functor N P.

Local Open Scope cat.

Definition is_iso_tensor_on_is_iso {C : monoidal_cat} {x y z w : C} {f : x --> z} (fiso : is_iso f) {g : y --> w} (giso : is_iso g)
  : is_iso (#(monoidal_cat_to_tensor C) (f #, g)).
Proof.
  apply functor_on_is_iso_is_iso.
  apply is_iso_binprod_cat_pair_of_is_iso.
  exact fiso.
  exact giso.
Defined.

Definition iso_tensor_on_iso {C : monoidal_cat} {x y z w : C} (f : iso x z) (g : iso y w) :
  iso (monoidal_cat_to_tensor C (x , y)) (monoidal_cat_to_tensor C (z , w)) :=
  isopair (#(monoidal_cat_to_tensor C) (f #, g)) (is_iso_tensor_on_is_iso (pr2 f) (pr2 g)).

Definition iso_functor_after_tensor_on_iso {C : monoidal_cat} {D : precategory} (H : C ⟶ D) {x y z w : C} (f : iso x z) (g : iso y w) :
  iso (H (monoidal_cat_to_tensor C (x , y))) (H (monoidal_cat_to_tensor C (z , w))).
Proof.
  apply functor_on_iso.
  exact (iso_tensor_on_iso f g).
Defined.

Definition iso_tensor_after_functor_on_iso {C : precategory} {D : monoidal_cat} (H : C ⟶ D) {x y z w : C} (f : iso x z) (g : iso y w) :
  iso (monoidal_cat_to_tensor D (H x , H y)) (monoidal_cat_to_tensor D (H z , H w)).
Proof.
  apply iso_tensor_on_iso.
  exact (functor_on_iso H f).
  exact (functor_on_iso H g).
Defined.

Definition family_of_iso_monoidal_functor_comp : ∏ x : ob (M × M),
  iso (tensor_after_functor M P (F ∙ G) x) (functor_after_tensor M P (F ∙ G) x).
Proof.
  intro x.
  exact (iso_comp (pr1 (monoidal_functor_to_nat_iso G) (F (x true) , F (x false))) (functor_on_iso G (pr1 (monoidal_functor_to_nat_iso F) x))).
Defined.

Lemma tensor_comp_to_tensor {x x' : ob (M × M)} (f : x --> x') : #(tensor_after_functor M P (F ∙ G)) f =
  (pr1 (monoidal_functor_to_nat_iso G) (F (x true) , F (x false)) · #G(#(tensor_after_functor M N F) f)) ·
  inv_from_iso (pr1 (monoidal_functor_to_nat_iso G) (F (x' true) , F (x' false))).
Proof.
  set (d := pr2 (monoidal_functor_to_nat_iso G) (F (x true) , F (x false)) (F (x' true) , F (x' false)) (#F (f true) #, #F (f false))).
  apply (comm_square_to_left_vertical_arrow _ _ _ _ d).
Defined.

Definition is_nat_iso_family_of_iso_monoidal_functor_comp :
  is_nat_iso (tensor_after_functor M P (F ∙ G)) (functor_after_tensor M P (F ∙ G)) family_of_iso_monoidal_functor_comp.
Proof.
  intros x x' f.
  rewrite (tensor_comp_to_tensor f).
  unfold family_of_iso_monoidal_functor_comp.
  transitivity (pr1 (monoidal_functor_to_nat_iso G) (F (x true), F (x false))·
  # G (#(tensor_after_functor M N (pr1 F)) f) · ((inv_from_iso (pr1 (monoidal_functor_to_nat_iso G) (F (x' true), F (x' false))) · pr1 (monoidal_functor_to_nat_iso G) (F (x' true), F (x' false))) · # G (pr1 (monoidal_functor_to_nat_iso F) x'))).
  - rewrite <- assoc. apply cancel_precomposition.
    rewrite <- assoc. reflexivity.
  - rewrite iso_after_iso_inv.
    rewrite id_left.
    transitivity (pr1 (monoidal_functor_to_nat_iso G) (F (x true), F (x false)) · #G (pr1 (monoidal_functor_to_nat_iso F) x) ·
                      #G (#(functor_after_tensor M N F) f)).
    rewrite <- assoc. symmetry. rewrite <- assoc. symmetry. apply cancel_precomposition.
    apply (functor_on_comm_square G _ _ _ _ (pr2 (monoidal_functor_to_nat_iso F) x x' f)).
    reflexivity.
Defined.

Definition nat_iso_monoidal_functor_comp :
  tensor_after_functor M P (functor_composite F G) ⇔ functor_after_tensor M P (functor_composite F G) :=
  tpair _ family_of_iso_monoidal_functor_comp is_nat_iso_family_of_iso_monoidal_functor_comp.

Notation "'e'" := (monoidal_cat_to_unit M).
Notation "'e''" := (monoidal_cat_to_unit N).
Notation "'e'''" := (monoidal_cat_to_unit P).

Definition iso_unit_to_unit_monoidal_functor_comp : iso e'' ((F ∙ G) e) :=
  iso_comp (monoidal_functor_to_iso_unit_to_unit G) (functor_on_iso G (monoidal_functor_to_iso_unit_to_unit F)).

Notation "'α'" := (monoidal_cat_to_associator M).
Notation "'α''" := (monoidal_cat_to_associator N).
Notation "a ⊗ b" := (monoidal_cat_to_tensor M (a , b)) (at level 31).
Notation "f #⊗ g" := (#(monoidal_cat_to_tensor M) (f #, g)) (at level 31).
Notation "a ⊗' b" := (monoidal_cat_to_tensor N (a , b)) (at level 31).
Notation "f #⊗' g" := (#(monoidal_cat_to_tensor N) (f #, g)) (at level 31).
Notation "a ⊗'' b" := (monoidal_cat_to_tensor P (a , b)) (at level 31).
Notation "f #⊗'' g" := (#(monoidal_cat_to_tensor P) (f #, g)) (at level 31).
Notation "'Φ'" := (monoidal_functor_to_nat_iso F).
Notation "'Φ''" := (monoidal_functor_to_nat_iso G).
Notation "'φ'" := (monoidal_functor_to_iso_unit_to_unit F).
Notation "'l''" := (monoidal_cat_to_left_unitor N).
Notation "'r''" := (monoidal_cat_to_right_unitor N).

Lemma image_of_comm_hexagon : ∏ a b c : M,
  #G (pr1 α' ((F a , F b) , F c)) · (#G (identity (F a) #⊗' (pr1 Φ (b , c))) · #G (pr1 Φ (a , b ⊗ c))) =
  #G ((pr1 Φ (a , b)) #⊗' identity (F c)) · #G (pr1 Φ (a ⊗ b , c)) · #G (#F (pr1 α ((a , b) , c))).
Proof.
  intros a b c.
  rewrite <- 4 (functor_comp G).
  apply maponpaths.
  apply (monoidal_functor_to_hexagon_eq F).
Defined.

Lemma image_of_comm_hexagon_to_image_of_comm_hexagon_with_inverse_left_horizontal_iso : ∏ a b c : M,
  inv_from_iso (isopair (#G ((pr1 Φ (a , b)) #⊗' identity (F c))) (pr2 (iso_functor_after_tensor_on_iso G (pr1 Φ (a , b)) (identity_iso (F c))))) · #G (pr1 α' ((F a, F b), F c)) · #G (identity (F a) #⊗' pr1 Φ (b, c)) · #G (pr1 Φ (a, b ⊗ c)) =
  #G (pr1 Φ (a ⊗ b , c)) · #G (#F (pr1 α ((a , b) , c))).
Proof.
  intros a b c.
  set (i := isopair (#G ((pr1 Φ (a , b)) #⊗' identity (F c))) (pr2 (iso_functor_after_tensor_on_iso G (pr1 Φ (a , b)) (identity_iso (F c))))). rewrite <- 2 assoc.
  apply (comm_hexagon_to_comm_hexagon_with_inverse_left_horizontal_iso _ _ _ _ _ i (image_of_comm_hexagon a b c)).
Defined.

Definition hexagon_eq_monoidal_functor_comp : hexagon_eq_3 M P (functor_composite F G) (nat_iso_monoidal_functor_comp).
Proof.
  intros a b c.
  unfold nat_iso_monoidal_functor_comp. cbn.
  rewrite <- (id_left (identity (G (F a)))).
  rewrite <- binprod_cat_comp.
  rewrite (functor_comp (monoidal_cat_to_tensor P)).
  transitivity (pr1 (monoidal_cat_to_associator P) ((G (F a), G (F b)), G (F c)) ·
  (# (monoidal_cat_to_tensor P) (identity (G (F a)) #, pr1 (monoidal_functor_to_nat_iso G) (F b, F c)) ·
  (# (monoidal_cat_to_tensor P) (identity (G (F a)) #, # G (pr1 Φ (b, c))) ·
  pr1 (monoidal_functor_to_nat_iso G) (F a, F (b ⊗ c))) ·
  # G (pr1 Φ (a, b ⊗ c)))).
  - apply cancel_precomposition.
    rewrite assoc. rewrite assoc4. reflexivity.
  - rewrite <- (functor_id G).
    change (pr1 (monoidal_cat_to_associator P) ((G (F a), G (F b)), G (F c)) ·
    (# (monoidal_cat_to_tensor P) (# G (identity (F a)) #, pr1 Φ' (F b, F c)) ·
    (# (tensor_after_functor N P G) (identity (F a) #, pr1 Φ (b, c)) ·
    pr1 Φ' (F a, F (b ⊗ c))) · # G (pr1 Φ (a, b ⊗ c))) =
    # (monoidal_cat_to_tensor P)
    (pr1 Φ' (F a, F b) · # G (pr1 Φ (a, b)) #, identity (G (F c))) ·
    (pr1 Φ' (F (a ⊗ b), F c) · # G (pr1 Φ (a ⊗ b, c))) ·
    # G (# F (pr1 α ((a, b), c)))).
    rewrite (pr2 Φ').
    rewrite <- assoc4. rewrite 2 assoc. rewrite (functor_id G). rewrite (monoidal_functor_to_hexagon_eq G).
    set (i := iso_functor_after_tensor_on_iso G (pr1 Φ (a , b)) (identity_iso (F c))).
    transitivity (# (monoidal_cat_to_tensor P)
    (pr1 (pr1 (pr2 G)) (F a, F b) #, identity ((pr1 G) (F c))) ·
    (# (tensor_after_functor N P (pr1 G)) (pr1 Φ (a, b) #, identity (F c)) ·
       pr1 Φ' ((functor_after_tensor M N (pr1 F)) (a, b), F c) ·
       inv_from_iso (isopair (pr1 i) (pr2 i))) ·
    # (pr1 G) (pr1 α' ((F a, F b), F c)) ·
    # (functor_after_tensor N P (pr1 G)) (identity (F a) #, pr1 Φ (b, c)) ·
    # G (pr1 Φ (a, b ⊗ c))).
    + apply cancel_postcomposition. apply cancel_postcomposition. apply cancel_postcomposition. apply cancel_precomposition.
      apply (comm_square_to_upper_horizontal_arrow _ _ _ (pr2 i) _ (pr2 Φ' _ _ (pr1 Φ (a , b) #, identity (F c)))).
    + transitivity (# (monoidal_cat_to_tensor P)
      (pr1 (pr1 (pr2 G)) (F a, F b) #, identity ((pr1 G) (F c))) ·
      # (tensor_after_functor N P (pr1 G)) (pr1 Φ (a, b) #, identity (F c)) ·
      pr1 Φ' ((functor_after_tensor M N (pr1 F)) (a, b), F c) ·
      (inv_from_iso (isopair (pr1 i) (pr2 i)) ·
      # (pr1 G) (pr1 α' ((F a, F b), F c)) ·
      # (functor_after_tensor N P (pr1 G)) (identity (F a) #, pr1 Φ (b, c)) ·
      # G (pr1 Φ (a, b ⊗ c))) ).
      * rewrite <- 6 assoc. rewrite 2 assoc. symmetry. rewrite <- 5 assoc. reflexivity.
      * symmetry. rewrite <- 2 assoc. symmetry.
        assert (p : inv_from_iso (isopair (pr1 i) (pr2 i)) · # (pr1 G) (pr1 α' ((F a, F b), F c)) ·
        # (functor_after_tensor N P (pr1 G)) (identity (F a) #, pr1 Φ (b, c)) ·
        # G (pr1 Φ (a, b ⊗ c)) = # G (pr1 Φ (a ⊗ b, c)) · # G (# F (pr1 α ((a, b), c)))).
        apply (image_of_comm_hexagon_to_image_of_comm_hexagon_with_inverse_left_horizontal_iso a b c).
        rewrite p.
        unfold tensor_after_functor, tensor_after_functor_data, tensor_after_functor_mor. cbn.
        transitivity (# (monoidal_cat_to_tensor P) (pr1 Φ' (F a, F b) · # G (pr1 Φ (a, b)) #, identity (G (F c))) ·
        pr1 Φ' (functor_after_tensor_ob M N (pr1 F) (a, b), F c) · (# G (pr1 Φ (a ⊗ b, c)) · # G (# F (pr1 α ((a, b), c))))).
        symmetry. rewrite <- (id_left (identity (G (F c)))).
        assert (q : (pr1 Φ' (F a, F b) · # G (pr1 Φ (a, b)) #, identity (G (F c)) · identity (G (F c))) =
                    (pr1 Φ' (F a, F b) #, identity (G (F c))) · (#G (pr1 Φ (a, b)) #, identity (G (F c)))).
        symmetry. apply binprod_cat_comp.
        rewrite q.
        rewrite (functor_comp (monoidal_cat_to_tensor P)). rewrite functor_id. reflexivity.
        rewrite <- assoc. reflexivity.
Defined.

Definition square_eq_1_monoidal_functor_comp : square_eq_1 M P (functor_composite F G) (nat_iso_monoidal_functor_comp) iso_unit_to_unit_monoidal_functor_comp .
Proof.
  unfold square_eq_1.
  intro a.
  unfold nat_iso_monoidal_functor_comp. cbn.
  rewrite assoc.
  unfold iso_unit_to_unit_monoidal_functor_comp.
  rewrite <- (id_left (identity (G (F a)))).
  rewrite <- (binprod_cat_comp).
  rewrite (functor_comp (monoidal_cat_to_tensor P)).
  rewrite <- assoc.
  rewrite <- (functor_id G).
  change (# (monoidal_cat_to_tensor P)
  (monoidal_functor_to_iso_unit_to_unit G #, # G (identity (F a))) ·
  # (tensor_after_functor N P (pr1 G))
  (φ #, identity (F a)) · pr1 Φ' ((pr1 F) e, F a) · (# G (pr1 Φ (e, a)) · # G
  (# F (pr1 (monoidal_cat_to_left_unitor M) a))) =
  pr1 (monoidal_cat_to_left_unitor P) (G (F a))).
  transitivity (# (monoidal_cat_to_tensor P)
  (monoidal_functor_to_iso_unit_to_unit G #, # G (identity (F a))) ·
  (pr1 Φ' (e', F a) · #(functor_after_tensor N P G) (φ #, identity (F a))) · (# G (pr1 Φ (e, a)) ·
  # G (# F (pr1 (monoidal_cat_to_left_unitor M) a))) ).
  - apply cancel_postcomposition.
    rewrite <- assoc. apply cancel_precomposition.
    apply (pr2 Φ' _ _ (φ #, identity (F a))).
  - rewrite <- 2 assoc.
    transitivity ( # (monoidal_cat_to_tensor P)
    (monoidal_functor_to_iso_unit_to_unit G #, # G (identity (F a))) ·
    (pr1 Φ' (e', F a) · #G (pr1 l' (F a)))).
    apply cancel_precomposition. apply cancel_precomposition.
    change ((# G (# (monoidal_cat_to_tensor N) (pr1 (pr2 (pr2 F)) #, identity ((pr1 F) a))) ·
    (# G (pr1 Φ (e, a)) · # G (# F (pr1 (monoidal_cat_to_left_unitor M) a))) =
             # G (pr1 l' (F a)))).
    rewrite  assoc.
    apply (functor_on_comm_square_with_reverse_vertical_arrows G _ _ _ _ (monoidal_functor_to_square_eq_1 F a)).
    rewrite assoc.
    rewrite (functor_id G).
    apply (monoidal_functor_to_square_eq_1 G (F a)).
Defined.

Definition square_eq_2_monoidal_functor_comp : square_eq_2 M P (functor_composite F G) (nat_iso_monoidal_functor_comp) iso_unit_to_unit_monoidal_functor_comp .
Proof.
  unfold square_eq_2.
  intro a.
  unfold nat_iso_monoidal_functor_comp. cbn.
  rewrite assoc.
  unfold iso_unit_to_unit_monoidal_functor_comp.
  rewrite <- (id_left (identity (G (F a)))).
  rewrite <- (binprod_cat_comp).
  rewrite (functor_comp (monoidal_cat_to_tensor P)).
  rewrite <- assoc.
  rewrite <- (functor_id G).
  change (# (monoidal_cat_to_tensor P)
  (# G (identity (F a)) #, monoidal_functor_to_iso_unit_to_unit G) ·
  # (tensor_after_functor N P (pr1 G))
  (identity (F a) #, φ) · pr1 Φ' (F a, F e) · (# G (pr1 Φ (a, e)) · # G
  (# F (pr1 (monoidal_cat_to_right_unitor M) a))) =
  pr1 (monoidal_cat_to_right_unitor P) (G (F a))).
  transitivity (# (monoidal_cat_to_tensor P)
  (# G (identity (F a)) #, monoidal_functor_to_iso_unit_to_unit G) ·
  (pr1 Φ' (F a, e') · #(functor_after_tensor N P G) (identity (F a) #, φ)) · (# G (pr1 Φ (a, e)) ·
  # G (# F (pr1 (monoidal_cat_to_right_unitor M) a))) ).
  - apply cancel_postcomposition.
    rewrite <- assoc. apply cancel_precomposition.
    apply (pr2 Φ' _ _ (identity (F a) #, φ)).
  - rewrite <- 2 assoc.
    transitivity ( # (monoidal_cat_to_tensor P)
    (# G (identity (F a)) #, monoidal_functor_to_iso_unit_to_unit G) ·
    (pr1 Φ' (F a, e') · #G (pr1 r' (F a)))).
    apply cancel_precomposition. apply cancel_precomposition.
    change ((# G (# (monoidal_cat_to_tensor N) (identity ((pr1 F) a) #, pr1 (pr2 (pr2 F)))) ·
    (# G (pr1 Φ (a, e)) · # G (# F (pr1 (monoidal_cat_to_right_unitor M) a))) =
             # G (pr1 r' (F a)))).
    rewrite  assoc.
    apply (functor_on_comm_square_with_reverse_vertical_arrows G _ _ _ _ (monoidal_functor_to_square_eq_2 F a)).
    rewrite assoc.
    rewrite (functor_id G).
    apply (monoidal_functor_to_square_eq_2 G (F a)).
Defined.

End monoidal_composition.

Definition monoidal_functor_comp_struct {M N P : monoidal_cat} (F : monoidal_functor M N) (G : monoidal_functor N P) :
  monoidal_functor_struct M P (functor_composite F G).
Proof.
  use tpair.
  - exact (nat_iso_monoidal_functor_comp M N P F G).
  - use tpair.
    + exact (iso_unit_to_unit_monoidal_functor_comp M N P F G).
    + use tpair.
      * exact (hexagon_eq_monoidal_functor_comp M N P F G).
      * exact (tpair _ (square_eq_1_monoidal_functor_comp M N P F G) (square_eq_2_monoidal_functor_comp M N P F G)).
Defined.

Definition monoidal_functor_comp {M N P : monoidal_cat} (F : monoidal_functor M N) (G : monoidal_functor N P) : monoidal_functor M P :=
  tpair _ (functor_composite F G) (monoidal_functor_comp_struct F G).


Section braided_composition.

Variables M N P : braided_monoidal_cat.

Variable F : braided_monoidal_functor M N.
Variable G : braided_monoidal_functor N P.

Notation "'γ'" := (braided_monoidal_cat_to_braiding M).
Notation "'γ''" := (braided_monoidal_cat_to_braiding N).
Notation "'γ'''" := (braided_monoidal_cat_to_braiding P).

Definition compatibility_with_braidings_monoidal_functor_comp : compatibility_with_braidings M P (monoidal_functor_comp F G).
Proof.
  unfold compatibility_with_braidings.
  intros a b. cbn.
  rewrite <- assoc.
  transitivity (pr1 (monoidal_functor_to_nat_iso G) (F a, F b) · (# G (pr1 γ' (F a, F b)) · # G (pr1 (monoidal_functor_to_nat_iso F) (b, a)))).
  - apply cancel_precomposition.
    apply (functor_on_comm_square G _ _ _ _ (braided_monoidal_functor_to_compatibility_with_braidings F a b)).
  - rewrite 2 assoc. apply cancel_postcomposition.
    apply (braided_monoidal_functor_to_compatibility_with_braidings G (F a) (F b)).
Defined.

End braided_composition.

Definition braided_monoidal_functor_comp {M N P : braided_monoidal_cat} (F : braided_monoidal_functor M N) (G : braided_monoidal_functor N P)  := tpair _ (monoidal_functor_comp F G) (compatibility_with_braidings_monoidal_functor_comp M N P F G).

Definition symmetric_monoidal_functor_comp {M N P : symmetric_monoidal_cat} (F : symmetric_monoidal_functor M N)
  (G : symmetric_monoidal_functor N P) : symmetric_monoidal_functor M P := braided_monoidal_functor_comp F G.

Local Open Scope type_scope.

Definition monoidal_equivalence (M N : monoidal_cat) : UU :=
  ∑ F : monoidal_functor M N, ∑ G : monoidal_functor N M,
    monoidal_nat_iso (monoidal_functor_comp F G) (monoidal_functor_identity M) ×
    monoidal_nat_iso (monoidal_functor_comp G F) (monoidal_functor_identity N).

Definition braided_monoidal_equivalence (M N : braided_monoidal_cat) : UU :=
  ∑ F : braided_monoidal_functor M N, ∑ G : braided_monoidal_functor N M,
    braided_monoidal_nat_iso (braided_monoidal_functor_comp F G) (braided_monoidal_functor_identity M) ×
    braided_monoidal_nat_iso (braided_monoidal_functor_comp G F) (braided_monoidal_functor_identity N).

Definition symmetric_monoidal_equivalence (M N : symmetric_monoidal_cat) : UU :=
  ∑ F : symmetric_monoidal_functor M N, ∑ G : symmetric_monoidal_functor N M,
    symmetric_monoidal_nat_iso (symmetric_monoidal_functor_comp F G) (symmetric_monoidal_functor_identity M) ×
    symmetric_monoidal_nat_iso (symmetric_monoidal_functor_comp G F) (symmetric_monoidal_functor_identity N).


(** * Groupoids *)

Definition is_groupoid (C : precategory) := ∏ c d : C, ∏ f : c --> d, is_iso f.

Definition groupoid : UU := ∑ C : precategory, is_groupoid C.

Definition groupoid_to_cat (G : groupoid) : precategory := pr1 G.

Coercion groupoid_to_cat : groupoid >-> precategory.

(** * The underlying groupoid of a category *)

Definition hsubtype_ob_isos (C : precategory) : hsubtype (ob C) := fun c : C => htrue.

Definition hsubtype_mor_isos (C : precategory) : ∏ c d : C, hsubtype (C⟦c, d⟧) :=
  fun c d : C => (fun f : C⟦c, d⟧ => hProppair (is_iso f) (isaprop_is_iso c d f)).

Definition is_sub_category_isos (C : precategory) : is_sub_precategory (hsubtype_ob_isos C) (hsubtype_mor_isos C).
Proof.
  use dirprodpair.
  - intros c X. exact (identity_is_iso C c).
  - intros. simpl. intros a b c f g fiso giso. exact (is_iso_comp_of_isos (isopair f fiso) (isopair g giso)).
Defined.

Definition sub_category_of_isos (C : precategory) : sub_precategories C :=
  tpair _ (dirprodpair (hsubtype_ob_isos C) (hsubtype_mor_isos C)) (is_sub_category_isos C).

Definition sub_category_of_isos_to_groupoid (C : precategory) : groupoid.
Proof.
  use tpair.
  - exact (carrier_of_sub_precategory C (sub_category_of_isos C)).
  - simpl. unfold is_groupoid. intros.
    destruct f as [f p].
    assert (fiso : is_iso f). apply p.
    unfold is_iso. intro e.
    use gradth.
    intro g.