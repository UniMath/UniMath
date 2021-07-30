(** * Binary product of (pre)categories

  Benedikt Ahrens, Ralph Matthes, Peter LeFanu Lumsdaine

  SubstitutionSystems

  2015

  For the general case, see [product_precategory].

  See [unit_category] for the unit category, which is the unit
  under cartesian product up to isomorphism.

*)


(** ** Contents :

  - Definition of the cartesian product of two precategories

  - From a functor on a product of precategories to a functor on one of
    the categories by fixing the argument in the other component

  - From a functor on a product of precategories to a nat. transformation on one of
    the categories by fixing the morphism argument in the other component

  - Definition of the associator functors

  - Definition of the pair of two functors: A × C → B × D
    given A → B and C → D

  - Definition of the diagonal functor [bindelta_functor].

  - Definition of post-whiskering with parameter (with a functor on a
    product of precategories where one argument is seen as parameter)

*)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Local Open Scope cat.

Definition precategory_binproduct_mor (C D : precategory_ob_mor) (cd cd' : C × D) := pr1 cd --> pr1 cd' × pr2 cd --> pr2 cd'.

Definition precategory_binproduct_ob_mor (C D : precategory_ob_mor) : precategory_ob_mor
  := tpair _ _ (precategory_binproduct_mor C D).

Definition precategory_binproduct_data (C D : precategory_data) : precategory_data.
Proof.
  exists (precategory_binproduct_ob_mor C D).
  split.
  - intro cd.
    exact (make_dirprod (identity (pr1 cd)) (identity (pr2 cd))).
  - intros cd cd' cd'' fg fg'.
    exact (make_dirprod (pr1 fg · pr1 fg') (pr2 fg · pr2 fg')).
Defined.

Section precategory_binproduct.

Variables C D : precategory.

Lemma is_precategory_precategory_binproduct_data : is_precategory (precategory_binproduct_data C D).
Proof.
  repeat split; intros.
  - apply dirprodeq; apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
  - apply dirprodeq; apply assoc'.
Defined. (** needed for the op-related goal below *)

Definition precategory_binproduct : precategory
  := tpair _ _ is_precategory_precategory_binproduct_data.

Definition has_homsets_precategory_binproduct (hsC : has_homsets C) (hsD : has_homsets D) :
  has_homsets precategory_binproduct.
Proof.
  intros a b.
  apply isasetdirprod.
  - apply hsC.
  - apply hsD.
Qed.

Definition ob1 (x : precategory_binproduct) : C := pr1 x.
Definition ob2 (x : precategory_binproduct) : D := pr2 x.
Definition mor1 (x x' : precategory_binproduct) (f : _ ⟦x, x'⟧) : _ ⟦ob1 x, ob1 x'⟧ := pr1 f.
Definition mor2 (x x' : precategory_binproduct) (f : _ ⟦x, x'⟧) : _ ⟦ob2 x, ob2 x'⟧ := pr2 f.

End precategory_binproduct.

Arguments ob1 { _ _ } _ .
Arguments ob2 { _ _ } _ .
Arguments mor1 { _ _ _ _ } _ .
Arguments mor2 { _ _ _ _ } _ .
Local Notation "C × D" := (precategory_binproduct C D) (at level 75, right associativity).


Goal ∏ (C D:precategory), (C × D)^op = (C^op × D^op).
  reflexivity.
Qed.


(** Objects and morphisms in the product precategory of two precategories *)
Definition make_precatbinprod {C D : precategory} (X : C) (Y : D) : precategory_binproduct C D
  := make_dirprod X Y.

Local Notation "A ⊗ B" := (make_precatbinprod A B).
Local Notation "( A , B )" := (make_precatbinprod A B).

Definition precatbinprodmor {C D : precategory} {X X' : C} {Z Z' : D} (α : X --> X') (β : Z --> Z')
  : X ⊗ Z --> X' ⊗ Z'
  := make_dirprod α β.

Local Notation "( f #, g )" := (precatbinprodmor f g).

(* Some useful facts about product precategories *)
Definition binprod_id {C D : precategory} (c : C) (d : D) : (identity c #, identity d) = identity (c, d).
Proof.
  apply idpath.
Defined.

Definition binprod_comp {C D : precategory} (c c' c'' : C) (d d' d'' : D) (f : c --> c') (f' : c' --> c'') (g : d --> d') (g' : d' --> d'') : (f · f' #, g · g') = (f #, g) · (f' #, g').
Proof.
  apply idpath.
Defined.

Lemma is_iso_binprod_iso_aux {C D : precategory} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_iso f)
  (g_is_iso : is_iso g) : is_inverse_in_precat (f #, g)
        (inv_from_iso (make_iso f f_is_iso) #, inv_from_iso (make_iso g g_is_iso)).
Proof.
  apply make_dirprod.
  - transitivity ((make_iso f f_is_iso) · (inv_from_iso (make_iso f f_is_iso)) #, (make_iso g g_is_iso) · (inv_from_iso (make_iso g g_is_iso))).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_inv_after_iso.
      apply binprod_id.
  - transitivity ((inv_from_iso (make_iso f f_is_iso)) · (make_iso f f_is_iso) #, (inv_from_iso (make_iso g g_is_iso)) · (make_iso g g_is_iso)).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_after_iso_inv.
      apply binprod_id.
Qed.

Definition is_iso_binprod_iso {C D : precategory} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_iso f)
  (g_is_iso : is_iso g) : is_iso (f #, g).
Proof.
  apply (is_iso_qinv (f #, g) (inv_from_iso (make_iso f f_is_iso) #, inv_from_iso (make_iso g g_is_iso))).
  apply is_iso_binprod_iso_aux.
Defined.

(** Isos in product precategories *)
Definition precatbinprodiso {C D : precategory} {X X' : C} {Z Z' : D} (α : iso X X') (β : iso Z Z')
  : iso (X ⊗ Z) (X' ⊗ Z').
Proof.
  set (f := precatbinprodmor α β).
  set (g := precatbinprodmor (iso_inv_from_iso α) (iso_inv_from_iso β)).
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

Definition precatbinprodiso_inv {C D : precategory} {X X' : C} {Z Z' : D}
  (α : iso X X') (β : iso Z Z')
  : precatbinprodiso (iso_inv_from_iso α) (iso_inv_from_iso β)
  = iso_inv_from_iso (precatbinprodiso α β).
Proof.
  apply inv_iso_unique.
  apply pathsdirprod.
  - apply iso_inv_after_iso.
  - apply iso_inv_after_iso.
Defined.

Definition is_z_iso_binprod_z_iso {C D : precategory} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_z_iso : is_z_isomorphism f)
  (g_is_z_iso : is_z_isomorphism g) : is_z_isomorphism (f #, g).
Proof.
  red.
  exists (is_z_isomorphism_mor f_is_z_iso,,is_z_isomorphism_mor g_is_z_iso).
  red.
  split; apply dirprodeq; cbn.
  - apply (pr1 (pr2 f_is_z_iso)).
  - apply (pr1 (pr2 g_is_z_iso)).
  - apply (pr2 (pr2 f_is_z_iso)).
  - apply (pr2 (pr2 g_is_z_iso)).
Defined.

(** Associativity functors *)
Section assoc.

Definition precategory_binproduct_assoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2))
                 (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2).
Proof.
  use tpair.
  - intros c. exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
  - intros a b c. exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
Defined.

Definition precategory_binproduct_assoc (C0 C1 C2 : precategory)
  : (C0 × (C1 × C2)) ⟶ ((C0 × C1) × C2).
Proof.
  exists (precategory_binproduct_assoc_data _ _ _).
  abstract ( split; [ intros c; apply idpath | intros c0 c1 c2 f g; apply idpath] ).
Defined.

Definition precategory_binproduct_unassoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2)
                 (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2)).
Proof.
  use tpair.
  - intros c. exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
  - intros a b c. exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
Defined.

Definition precategory_binproduct_unassoc (C0 C1 C2 : precategory)
  : ((C0 × C1) × C2) ⟶ (C0 × (C1 × C2)).
Proof.
  exists (precategory_binproduct_unassoc_data _ _ _).
  abstract ( split; [ intros c; apply idpath | intros c0 c1 c2 f g; apply idpath] ).
Defined.

End assoc.

(** Fixing one argument of C × D -> E results in a functor *)
Section functor_fix_fst_arg.

Variable C D E : precategory.
Variable F : functor (precategory_binproduct C D) E.
Variable c : C.

Definition functor_fix_fst_arg_ob (d: D) : E := F (tpair _ c d).
Definition functor_fix_fst_arg_mor (d d' : D) (f : d --> d') : functor_fix_fst_arg_ob d --> functor_fix_fst_arg_ob d'.
Proof.
  apply (#F).
  exact (make_dirprod (identity c) f).
Defined.

Definition functor_fix_fst_arg_data : functor_data D E
  := tpair _ functor_fix_fst_arg_ob functor_fix_fst_arg_mor.

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
    assert (functor_comp_inst := @functor_comp _ _ F (make_dirprod c d) (make_dirprod c d') (make_dirprod c d'')).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_fst_arg : D ⟶ E
  := tpair _ functor_fix_fst_arg_data is_functor_functor_fix_fst_arg_data.

End functor_fix_fst_arg.

Section nat_trans_from_functor_fix_fst_morphism_arg.

Variable C D E : precategory.
Variable F : (C × D) ⟶ E.
Variable c c' : C.
Variable g: c --> c'.

Definition nat_trans_from_functor_fix_fst_morphism_arg_data (d: D): functor_fix_fst_arg C D E F c d --> functor_fix_fst_arg C D E F c' d.
Proof.
  apply (#F).
  exact (make_dirprod g (identity d)).
Defined.

Lemma nat_trans_from_functor_fix_fst_morphism_arg_ax: is_nat_trans _ _ nat_trans_from_functor_fix_fst_morphism_arg_data.
Proof.
  red.
  intros d d' f.
  unfold nat_trans_from_functor_fix_fst_morphism_arg_data.
  unfold functor_fix_fst_arg; cbn.
  unfold functor_fix_fst_arg_mor; simpl.
  eapply pathscomp0.
  2: { apply functor_comp. }
  apply pathsinv0.
  eapply pathscomp0.
  2: { apply functor_comp. }
  apply maponpaths.
  unfold compose.
  cbn.
  do 2 rewrite id_left.
  do 2 rewrite id_right.
  apply idpath.
Qed.

Definition nat_trans_from_functor_fix_fst_morphism_arg: functor_fix_fst_arg C D E F c ⟹ functor_fix_fst_arg C D E F c'.
Proof.
  use tpair.
  - intro d. apply nat_trans_from_functor_fix_fst_morphism_arg_data.
  - cbn. exact nat_trans_from_functor_fix_fst_morphism_arg_ax.
Defined.

End nat_trans_from_functor_fix_fst_morphism_arg.

Section nat_trans_fix_fst_arg.

Variable C D E : precategory.
Variable F F' : (C × D) ⟶ E.
Variable α : F ⟹ F'.
Variable c : C.

Definition nat_trans_fix_fst_arg_data (d: D): functor_fix_fst_arg C D E F c d --> functor_fix_fst_arg C D E F' c d := α (tpair _ c d).

Lemma nat_trans_fix_fst_arg_ax: is_nat_trans _ _ nat_trans_fix_fst_arg_data.
Proof.
  red.
  intros d d' f.
  unfold nat_trans_fix_fst_arg_data, functor_fix_fst_arg; simpl.
  unfold functor_fix_fst_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_fst_arg: functor_fix_fst_arg C D E F c ⟹ functor_fix_fst_arg C D E F' c
  := tpair _ nat_trans_fix_fst_arg_data nat_trans_fix_fst_arg_ax.

End nat_trans_fix_fst_arg.

Section functor_fix_snd_arg.

Variable C D E : precategory.
Variable F: (C × D) ⟶ E.
Variable d: D.

Definition functor_fix_snd_arg_ob (c: C): E := F (tpair _ c d).
Definition functor_fix_snd_arg_mor (c c': C)(f: c --> c'): functor_fix_snd_arg_ob c --> functor_fix_snd_arg_ob c'.
Proof.
  apply (#F).
  exact (make_dirprod f (identity d)).
Defined.

Definition functor_fix_snd_arg_data : functor_data C E
  := tpair _ functor_fix_snd_arg_ob functor_fix_snd_arg_mor.

Lemma is_functor_functor_fix_snd_arg_data: is_functor functor_fix_snd_arg_data.
Proof.
  split.
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
    assert (functor_comp_inst := @functor_comp _ _ F (make_dirprod c d) (make_dirprod c' d) (make_dirprod c'' d)).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_snd_arg: C ⟶ E.
Proof.
  exists functor_fix_snd_arg_data.
  exact is_functor_functor_fix_snd_arg_data.
Defined.

End functor_fix_snd_arg.

Section nat_trans_from_functor_fix_snd_morphism_arg.

Variable C D E : precategory.
Variable F : (C × D) ⟶ E.
Variable d d' : D.
Variable f: d --> d'.

Definition nat_trans_from_functor_fix_snd_morphism_arg_data (c: C): functor_fix_snd_arg C D E F d c --> functor_fix_snd_arg C D E F d' c.
Proof.
  apply (#F).
  exact (make_dirprod (identity c) f).
Defined.

Lemma nat_trans_from_functor_fix_snd_morphism_arg_ax: is_nat_trans _ _ nat_trans_from_functor_fix_snd_morphism_arg_data.
Proof.
  red.
  intros c c' g.
  unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
  unfold functor_fix_snd_arg; cbn.
  unfold functor_fix_snd_arg_mor; simpl.
  eapply pathscomp0.
  2: { apply functor_comp. }
  apply pathsinv0.
  eapply pathscomp0.
  2: { apply functor_comp. }
  apply maponpaths.
  unfold compose.
  cbn.
  do 2 rewrite id_left.
  do 2 rewrite id_right.
  apply idpath.
Qed.

Definition nat_trans_from_functor_fix_snd_morphism_arg: functor_fix_snd_arg C D E F d ⟹ functor_fix_snd_arg C D E F d'.
Proof.
  use tpair.
  - intro c. apply nat_trans_from_functor_fix_snd_morphism_arg_data.
  - cbn. exact nat_trans_from_functor_fix_snd_morphism_arg_ax.
Defined.

End nat_trans_from_functor_fix_snd_morphism_arg.

Section nat_trans_fix_snd_arg.

Variable C D E : precategory.
Variable F F': (C × D) ⟶ E.
Variable α: F ⟹ F'.
Variable d: D.

Definition nat_trans_fix_snd_arg_data (c:C): functor_fix_snd_arg C D E F d c --> functor_fix_snd_arg C D E F' d c := α (tpair _ c d).

Lemma nat_trans_fix_snd_arg_ax: is_nat_trans _ _ nat_trans_fix_snd_arg_data.
Proof.
  red.
  intros c c' f.
  unfold nat_trans_fix_snd_arg_data, functor_fix_snd_arg; simpl.
  unfold functor_fix_snd_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_snd_arg: functor_fix_snd_arg C D E F d ⟹ functor_fix_snd_arg C D E F' d
  := tpair _ nat_trans_fix_snd_arg_data nat_trans_fix_snd_arg_ax.

End nat_trans_fix_snd_arg.

(* Define pairs of functors and functors from pr1 and pr2 *)
Section functors.

Definition pair_functor_data {A B C D : precategory}
  (F : A ⟶ C) (G : B ⟶ D) : functor_data (A × B) (C × D).
Proof.
use tpair.
- intro x; apply (make_precatbinprod (F (pr1 x)) (G (pr2 x))).
- intros x y f; simpl; apply (precatbinprodmor (# F (pr1 f)) (# G (pr2 f))).
Defined.

Definition pair_functor {A B C D : precategory}
  (F : A ⟶ C) (G : B ⟶ D) : (A × B) ⟶ (C × D).
Proof.
apply (tpair _ (pair_functor_data F G)).
abstract (split;
  [ intro x; simpl; rewrite !functor_id; apply idpath
  | intros x y z f g; simpl; rewrite !functor_comp; apply idpath]).
Defined.

Definition pr1_functor_data (A B : precategory) :
  functor_data (A × B) A.
Proof.
use tpair.
- intro x; apply (pr1 x).
- intros x y f; simpl; apply (pr1 f).
Defined.

Definition pr1_functor (A B : precategory) : (A × B) ⟶ A.
Proof.
apply (tpair _ (pr1_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition pr2_functor_data (A B : precategory) :
  functor_data (A × B) B.
Proof.
use tpair.
- intro x; apply (pr2 x).
- intros x y f; simpl; apply (pr2 f).
Defined.

Definition pr2_functor (A B : precategory) : (A × B) ⟶ B.
Proof.
apply (tpair _ (pr2_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_functor_data (C : precategory) :
  functor_data C (C × C).
Proof.
use tpair.
- intro x; apply (make_precatbinprod x x).
- intros x y f; simpl; apply (precatbinprodmor f f).
Defined.

(* The diagonal functor Δ *)
Definition bindelta_functor (C : precategory) : C ⟶ (C × C).
Proof.
apply (tpair _ (bindelta_functor_data C)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_pair_functor_data (C D E : precategory)
  (F : C ⟶ D) (G : C ⟶ E) :
  functor_data C (precategory_binproduct D E).
Proof.
  use tpair.
  - intro c. apply (make_precatbinprod (F c) (G c)).
  - intros x y f. simpl. apply (precatbinprodmor (# F f) (# G f)).
Defined.

Lemma is_functor_bindelta_pair_functor_data (C D E : precategory)
  (F : C ⟶ D) (G : C ⟶ E) : is_functor (bindelta_pair_functor_data _ _ _ F G).
Proof.
  split.
  - intro c.
    simpl.
    rewrite functor_id.
    rewrite functor_id.
    apply idpath.
  - intros c c' c'' f g.
    simpl.
    rewrite functor_comp.
    rewrite functor_comp.
    apply idpath.
Qed.

Definition bindelta_pair_functor {C D E : precategory}
  (F : C ⟶ D) (G : C ⟶ E) : C ⟶ (D × E).
Proof.
  apply (tpair _ (bindelta_pair_functor_data C D E F G)).
  apply is_functor_bindelta_pair_functor_data.
Defined.

(* A swapping functor σ : C × D → D × C. *)
Definition binswap_pair_functor {C D : precategory} : (C × D) ⟶ (D × C) :=
  pair_functor (pr2_functor C D) (pr1_functor C D) □ bindelta_functor (C × D).

(* Reversing the order of three arguments *)
Definition reverse_three_args {C D E : precategory} : ((C × D) × E) ⟶ ((E × D) × C).
Proof.
  use (functor_composite (precategory_binproduct_unassoc _ _ _)).
  use (functor_composite binswap_pair_functor).
  exact (pair_functor binswap_pair_functor (functor_identity _)).
Defined.

Lemma reverse_three_args_ok {C D E : precategory} :
  functor_on_objects (reverse_three_args(C:=C)(D:=D)(E:=E)) = λ c, ((pr2 c, pr2 (pr1 c)), pr1 (pr1 c)).
Proof.
  apply idpath.
Qed.

Lemma reverse_three_args_idempotent {C D E : category} :
  functor_composite (reverse_three_args(C:=C)(D:=D)(E:=E))(reverse_three_args(C:=E)(D:=D)(E:=C))
  = functor_identity _.
Proof.
  apply functor_eq.
  - repeat (apply has_homsets_precategory_binproduct; try apply homset_property).
  - use functor_data_eq.
    + cbn.
      intro cde.
      apply idpath.
    + intros cde1 cde2 f.
      cbn.
      apply idpath.
Qed.

End functors.

Section whiskering.

(** Postwhiskering with parameter *)

Definition nat_trans_data_post_whisker_fst_param {B C D P: precategory}
           {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  nat_trans_data (functor_composite (pair_functor (functor_identity _) G) K)
                 (functor_composite (pair_functor (functor_identity _) H) K) :=
  λ pb : P × B, #K ((identity (ob1 pb),, γ (ob2 pb)):
                      (P × C)⟦ob1 pb,, G(ob2 pb), ob1 pb,, H(ob2 pb)⟧).

Lemma is_nat_trans_post_whisker_fst_param {B C D P: precategory}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  is_nat_trans _ _ (nat_trans_data_post_whisker_fst_param γ K).
Proof.
  intros pb pb' f.
  cbn.
  unfold nat_trans_data_post_whisker_fst_param.
  eapply pathscomp0.
  2: { apply functor_comp. }
  eapply pathscomp0.
  { apply pathsinv0. apply functor_comp. }
  apply maponpaths.
  unfold compose; cbn.
  rewrite id_left. rewrite id_right.
  apply maponpaths.
  apply (nat_trans_ax γ).
Qed.

Definition post_whisker_fst_param {B C D P: precategory}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  (functor_composite (pair_functor (functor_identity _) G) K) ⟹
  (functor_composite (pair_functor (functor_identity _) H) K) :=
  make_nat_trans _ _ _ (is_nat_trans_post_whisker_fst_param γ K).


Definition nat_trans_data_post_whisker_snd_param {B C D P: precategory}
           {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  nat_trans_data (functor_composite (pair_functor G (functor_identity _)) K)
                 (functor_composite (pair_functor H (functor_identity _)) K) :=
  λ bp : B × P, #K ((γ (ob1 bp),, identity (ob2 bp)):
                      (C × P)⟦G(ob1 bp),, ob2 bp, H(ob1 bp),, ob2 bp⟧).

Lemma is_nat_trans_post_whisker_snd_param {B C D P: precategory}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  is_nat_trans _ _ (nat_trans_data_post_whisker_snd_param γ K).
Proof.
  intros bp bp' f.
  cbn.
  unfold nat_trans_data_post_whisker_snd_param.
  eapply pathscomp0.
  2: { apply functor_comp. }
  eapply pathscomp0.
  { apply pathsinv0. apply functor_comp. }
  apply maponpaths.
  unfold compose; cbn.
  rewrite id_left. rewrite id_right.
  apply (maponpaths (λ x, make_dirprod x (pr2 f))).
  apply (nat_trans_ax γ).
Qed.

Definition post_whisker_snd_param {B C D P: precategory}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  (functor_composite (pair_functor G (functor_identity _)) K) ⟹
  (functor_composite (pair_functor H (functor_identity _)) K) :=
  make_nat_trans _ _ _ (is_nat_trans_post_whisker_snd_param γ K).

End whiskering.
