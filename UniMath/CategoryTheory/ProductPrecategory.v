
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of the cartesian product of two precategories
-    From a functor on a product of precategories to a functor on one of the categories by fixing the argument in the other component



************************************************************)


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G ∙ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(* Imported from Peter Lumsdaine's old bicategory code: *)

Section Dirproduct_utils.
(** * Utility functions on direct products of types. *)

(** The next few are either aliases or very mild generalisations of existing functions from the UniMath libraries.  They differ generally in using projections instead of destructing, making them apply and/or reduce in more situations.  The aliases are included just to standardise local naming conventions. *)

Notation "( x , y , .. , z )" := (dirprodpair .. (dirprodpair x y) .. z).

(** Compare [pathsdirprod]. *)
Definition dirproduct_paths {A B : Type} {p q : A × B}
  : pr1 p = pr1 q -> pr2 p = pr2 q -> p = q.
Proof.
  destruct p as [a b], q as [a' b']; apply pathsdirprod.
Defined.

(** Compare [total2asstol]. *)
Definition dirproduct_assoc {C0 C1 C2 : Type}
  : (C0 × (C1 × C2)) -> ((C0 × C1) × C2).
Proof.
  intros c. exact ((pr1 c , (pr1 (pr2 c))) , pr2 (pr2 c)).
Defined.

Definition dirproduct_unassoc {C0 C1 C2 : Type}
  : ((C0 × C1) × C2) -> (C0 × (C1 × C2)).
Proof.
  intros c. exact (pr1 (pr1 c) , ((pr2 (pr1 c)) , pr2 c)).
Defined.

(** Identical to [dirprodf]. *)
Definition dirproduct_maps {A0 A1 B0 B1} (f0 : A0 -> B0) (f1 : A1 -> B1)
  : A0 × A1 -> B0 × B1.
Proof.
  intros aa. exact (f0 (pr1 aa), f1 (pr2 aa)).
Defined.

(** Compare [prodtofuntoprod]. *)
Definition dirproduct_pair_maps {A B0 B1} (f0 : A -> B0) (f1 : A -> B1)
  : A -> B0 × B1.
Proof.
  intros a; exact (f0 a, f1 a).
Defined.

End Dirproduct_utils.

Definition product_precategory_ob_mor (C D : precategory_ob_mor) : precategory_ob_mor.
Proof.
  exists (C × D).
  exact (λ cd cd', pr1 cd ⇒ pr1 cd' × pr2 cd ⇒ pr2 cd').
Defined.

Definition product_precategory_data (C D : precategory_data) : precategory_data.
Proof.
  exists (product_precategory_ob_mor C D).
  split.
  - intro cd.
    exact (dirprodpair (identity (pr1 cd)) (identity (pr2 cd))).
  - intros cd cd' cd'' fg fg'.
    exact (dirprodpair (pr1 fg ;; pr1 fg') (pr2 fg ;; pr2 fg')).
Defined.

Section one_product_precategory.

Variables C D : precategory.

Lemma is_precategory_product_precategory_data : is_precategory (product_precategory_data C D).
Proof.
  repeat split; simpl; intros.
  - apply dirprodeq; apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
Qed.

Definition product_precategory : precategory
  := tpair _ _ is_precategory_product_precategory_data.

Definition has_homsets_product_precategory (hsC : has_homsets C) (hsD : has_homsets D) :
  has_homsets product_precategory.
Proof.
  intros a b.
  apply isasetdirprod.
  - apply hsC.
  - apply hsD.
Qed.

Section functor_fix_fst_arg.

Variable E : precategory.
Variable F: functor product_precategory E.
Variable c : C.

Definition functor_fix_fst_arg_ob (d:D): E := F(tpair _ c d).
Definition functor_fix_fst_arg_mor (d d':D)(f: d ⇒ d'): functor_fix_fst_arg_ob d ⇒ functor_fix_fst_arg_ob d'.
Proof.
  apply (#F).
  split; simpl.
  exact (identity c).
  exact f.
Defined.
Definition functor_fix_fst_arg_data : functor_data D E.
Proof.
  red.
  exists functor_fix_fst_arg_ob.
  exact functor_fix_fst_arg_mor.
Defined.

Lemma is_functor_functor_fix_fst_arg_data: is_functor functor_fix_fst_arg_data.
Proof.
  red.
  split; red.
  + intros d.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    unfold functor_fix_fst_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  + intros d d' d'' f g.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    assert (functor_comp_inst := functor_comp F (dirprodpair c d) (dirprodpair c d') (dirprodpair c d'')).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold product_precategory; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_fst_arg: functor D E.
Proof.
  exists functor_fix_fst_arg_data.
  exact is_functor_functor_fix_fst_arg_data.
Defined.

End functor_fix_fst_arg.

Section nat_trans_fix_fst_arg.

Variable E : precategory.
Variable F F': functor product_precategory E.
Variable α: F ⟶ F'.
Variable c: C.

Definition nat_trans_fix_fst_arg_data (d:D): functor_fix_fst_arg E F c d ⇒ functor_fix_fst_arg E F' c d := α (tpair _ c d).

Lemma nat_trans_fix_fst_arg_ax: is_nat_trans _ _ nat_trans_fix_fst_arg_data.
Proof.
  red.
  intros d d' f.
  unfold nat_trans_fix_fst_arg_data, functor_fix_fst_arg; simpl.
  unfold functor_fix_fst_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_fst_arg: functor_fix_fst_arg E F c ⟶ functor_fix_fst_arg E F' c.
Proof.
  exists nat_trans_fix_fst_arg_data.
  exact nat_trans_fix_fst_arg_ax.
Defined.

End nat_trans_fix_fst_arg.

Section functor_fix_snd_arg.

Variable E : precategory.
Variable F: functor product_precategory E.
Variable d: D.

Definition functor_fix_snd_arg_ob (c:C): E := F(tpair _ c d).
Definition functor_fix_snd_arg_mor (c c':C)(f: c ⇒ c'): functor_fix_snd_arg_ob c ⇒ functor_fix_snd_arg_ob c'.
Proof.
  apply (#F).
  split; simpl.
  exact f.
  exact (identity d).
Defined.
Definition functor_fix_snd_arg_data : functor_data C E.
Proof.
  red.
  exists functor_fix_snd_arg_ob.
  exact functor_fix_snd_arg_mor.
Defined.

Lemma is_functor_functor_fix_snd_arg_data: is_functor functor_fix_snd_arg_data.
Proof.
  red.
  split; red.
  + intros c.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    unfold functor_fix_snd_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  + intros c c' c'' f g.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    assert (functor_comp_inst := functor_comp F (dirprodpair c d) (dirprodpair c' d) (dirprodpair c'' d)).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold product_precategory; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_snd_arg: functor C E.
Proof.
  exists functor_fix_snd_arg_data.
  exact is_functor_functor_fix_snd_arg_data.
Defined.

End functor_fix_snd_arg.

Section nat_trans_fix_snd_arg.

Variable E : precategory.
Variable F F': functor product_precategory E.
Variable α: F ⟶ F'.
Variable d: D.

Definition nat_trans_fix_snd_arg_data (c:C): functor_fix_snd_arg E F d c ⇒ functor_fix_snd_arg E F' d c := α (tpair _ c d).

Lemma nat_trans_fix_snd_arg_ax: is_nat_trans _ _ nat_trans_fix_snd_arg_data.
Proof.
  red.
  intros c c' f.
  unfold nat_trans_fix_snd_arg_data, functor_fix_snd_arg; simpl.
  unfold functor_fix_snd_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_snd_arg: functor_fix_snd_arg E F d ⟶ functor_fix_snd_arg E F' d.
Proof.
  exists nat_trans_fix_snd_arg_data.
  exact nat_trans_fix_snd_arg_ax.
Defined.

End nat_trans_fix_snd_arg.


End one_product_precategory.

(** Objects and morphisms in the product precategory of two precategories *)
Definition prodcatpair {C D : precategory} (X : C) (Y : D) : product_precategory C D.
Proof.
  exists X.
  exact Y.
Defined.
Local Notation "A ⊗ B" := (prodcatpair A B) (at level 10).
Definition prodcatmor {C D : precategory} {X X' : C} {Z Z' : D} (α : X ⇒ X') (β : Z ⇒ Z')
  : X ⊗ Z ⇒ X' ⊗ Z'.
Proof.
  exists α.
  exact β.
Defined.

(** Isos in product precategories *)
Definition prodcatiso {C D : precategory} {X X' : C} {Z Z' : D} (α : iso X X') (β : iso Z Z')
  : iso (X ⊗ Z) (X' ⊗ Z').
Proof.
  set (f := prodcatmor α β).
  set (g := prodcatmor (iso_inv_from_iso α) (iso_inv_from_iso β)).
  exists f.
  apply (is_iso_qinv f g).
  use tpair.
  - apply pathsdirprod.
    apply iso_inv_after_iso.
    apply iso_inv_after_iso.
  - apply pathsdirprod.
    apply iso_after_iso_inv.
    apply iso_after_iso_inv.
Defined.


(* Imported from Peter Lumsdaine's old bicategory code: *)

Local Notation "C × D" := (product_precategory C D) (at level 75, right associativity) : precategory_scope.

Open Scope precategory_scope.
Delimit Scope precategory_scope with precat.

Definition unit_precategory : precategory.
Proof.
  use tpair. use tpair.
  (* ob, mor *) exists unit. intros; exact unit.
  (* identity, comp *) split; intros; constructor.
  (* id_left *) simpl; split; try split; intros; apply isconnectedunit.
Defined.

Definition unit_functor C : functor C unit_precategory.
Proof.
  use tpair. use tpair.
  (* functor_on_objects *) intros; exact tt.
  (* functor_on_morphisms *) intros F a b; apply identity.
  split.
  (* functor_id *) intros x; apply paths_refl.
  (* functor_comp *) intros x y z w v; apply paths_refl.
Defined.

(* TODO: perhaps generalise to constant functors? *)
Definition ob_as_functor_data {C : precategory_data} (c : C) : functor_data unit_precategory C.
Proof.
  use tpair.
  (* functor_on_objects *) intros; exact c.
  (* functor_on_morphisms *) intros F a b; apply identity.
Defined.

Definition ob_as_functor {C : precategory} (c : C) : functor unit_precategory C.
Proof.
  exists (ob_as_functor_data c).
  split.
  (* functor_id *) intros; constructor.
  (* functor_comp *) intros x y z w v; simpl. apply pathsinv0, id_left.
Defined.

Definition product_precategory_assoc_data (C0 C1 C2 : precategory_data)
  : functor_data (product_precategory_data C0 (product_precategory_data C1 C2))
                 (product_precategory_data (product_precategory_data C0 C1) C2).
Proof.
  (* functor_on_objects *) exists dirproduct_assoc.
  (* functor_on_morphisms *) intros a b; apply dirproduct_assoc.
Defined.

Definition product_precategory_assoc (C0 C1 C2 : precategory)
  : functor (C0 × (C1 × C2)) ((C0 × C1) × C2).
Proof.
  exists (product_precategory_assoc_data _ _ _). split.
  (* functor_id *) intros c. simpl; apply paths_refl.
  (* functor_comp *) intros c0 c1 c2 f g. simpl; apply paths_refl.
Defined.

Definition product_precategory_unassoc_data (C0 C1 C2 : precategory_data)
  : functor_data (product_precategory_data (product_precategory_data C0 C1) C2)
                 (product_precategory_data C0 (product_precategory_data C1 C2)).
Proof.
  (* functor_on_objects *) exists dirproduct_unassoc.
  (* functor_on_morphisms *) intros a b; apply dirproduct_unassoc.
Defined.

Definition product_precategory_unassoc (C0 C1 C2 : precategory)
  : functor ((C0 × C1) × C2) (C0 × (C1 × C2)).
Proof.
  exists (product_precategory_unassoc_data _ _ _). split.
  (* functor_id *) intros c. simpl; apply paths_refl.
  (* functor_comp *) intros c0 c1 c2 f g. simpl; apply paths_refl.
Defined.

Definition product_functor_data {C0 C1 D0 D1 : precategory_data}
  (F0 : functor_data C0 D0) (F1 : functor_data C1 D1)
: functor_data (product_precategory_data C0 C1) (product_precategory_data D0 D1).
Proof.
  (* functor_on_objects *) exists (dirproduct_maps F0 F1).
  (* functor_on_morphisms *) intros a b.
    apply dirproduct_maps; apply functor_on_morphisms.
Defined.

Definition product_functor {C0 C1 D0 D1 : precategory}
  (F0 : functor C0 D0) (F1 : functor C1 D1)
: functor (C0 × C1) (D0 × D1).
Proof.
  exists (product_functor_data F0 F1); split.
  (* functor_id *) intros c. apply dirproduct_paths; apply functor_id.
  (* functor_comp *) intros c0 c1 c2 f g.
    apply dirproduct_paths; apply functor_comp.
Defined.

Definition pair_functor_data {C D0 D1 : precategory_data}
  (F0 : functor_data C D0) (F1 : functor_data C D1)
: functor_data C (product_precategory_data D0 D1).
Proof.
  (* functor_on_objects *) exists (dirproduct_pair_maps F0 F1).
  (* functor_on_morphisms *) intros a b.
    apply dirproduct_pair_maps; apply functor_on_morphisms.
Defined.

Definition pair_functor {C D0 D1 : precategory}
  (F0 : functor C D0) (F1 : functor C D1)
: functor C (D0 × D1).
Proof.
  exists (pair_functor_data F0 F1); split.
  (* functor_id *) intros c. apply dirproduct_paths; apply functor_id.
  (* functor_comp *) intros c0 c1 c2 f g.
    apply dirproduct_paths; apply functor_comp.
Defined.
