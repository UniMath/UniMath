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


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
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

End precategory_binproduct.


Definition category_binproduct (C D : category) : category :=
    make_category (precategory_binproduct C D) (has_homsets_precategory_binproduct C D C D).

Definition ob1 {C D} (x : category_binproduct C D) : C := pr1 x.
Definition ob2 {C D} (x : category_binproduct C D) : D := pr2 x.
Definition mor1 {C D} (x x' : category_binproduct C D) (f : _ ⟦x, x'⟧) : _ ⟦ob1 x, ob1 x'⟧ := pr1 f.
Definition mor2 {C D} (x x' : category_binproduct C D) (f : _ ⟦x, x'⟧) : _ ⟦ob2 x, ob2 x'⟧ := pr2 f.

Arguments ob1 { _ _ } _ .
Arguments ob2 { _ _ } _ .
Arguments mor1 { _ _ _ _ } _ .
Arguments mor2 { _ _ _ _ } _ .
Local Notation "C × D" := (category_binproduct C D) (at level 75, right associativity).



(** Objects and morphisms in the product precategory of two precategories *)
Definition make_catbinprod {C D : category} (X : C) (Y : D) : category_binproduct C D
  := make_dirprod X Y.

Local Notation "A ⊗ B" := (make_catbinprod A B).
Local Notation "( A , B )" := (make_catbinprod A B).

Definition catbinprodmor {C D : category} {X X' : C} {Z Z' : D} (α : X --> X') (β : Z --> Z')
  : X ⊗ Z --> X' ⊗ Z'
  := make_dirprod α β.

Local Notation "( f #, g )" := (catbinprodmor f g).

(* Some useful facts about product precategories *)
Lemma binprod_id {C D : category} (c : C) (d : D) : (identity c #, identity d) = identity (c, d).
Proof.
  apply idpath.
Defined. (** this seems useful since one often has to tell Coq explicitly to make that conversion *)

Lemma binprod_comp {C D : category} (c c' c'' : C) (d d' d'' : D) (f : c --> c') (f' : c' --> c'') (g : d --> d') (g' : d' --> d'') : (f · f' #, g · g') = (f #, g) · (f' #, g').
Proof.
  apply idpath.
Defined. (** idem concerning Defined vs. Qed *)

Lemma is_iso_binprod_iso_aux {C D : category} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_iso f)
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

Definition is_iso_binprod_iso {C D : category} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_iso f)
  (g_is_iso : is_iso g) : is_iso (f #, g).
Proof.
  apply (is_iso_qinv (f #, g) (inv_from_iso (make_iso f f_is_iso) #, inv_from_iso (make_iso g g_is_iso))).
  apply is_iso_binprod_iso_aux.
Defined.

(** Isos in product precategories *)
Definition precatbinprodiso {C D : category} {X X' : C} {Z Z' : D} (α : iso X X') (β : iso Z Z')
  : iso (X ⊗ Z) (X' ⊗ Z').
Proof.
  set (f := catbinprodmor α β).
  set (g := catbinprodmor (iso_inv_from_iso α) (iso_inv_from_iso β)).
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

Definition precatbinprodiso_inv {C D : category} {X X' : C} {Z Z' : D}
  (α : iso X X') (β : iso Z Z')
  : precatbinprodiso (iso_inv_from_iso α) (iso_inv_from_iso β)
  = iso_inv_from_iso (precatbinprodiso α β).
Proof.
  apply inv_iso_unique.
  apply pathsdirprod.
  - apply iso_inv_after_iso.
  - apply iso_inv_after_iso.
Defined.

Definition is_z_iso_binprod_z_iso {C D : category} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_z_iso : is_z_isomorphism f)
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

Definition precatbinprod_z_iso {C D : category} {X X' : C} {Z Z' : D} (α : z_iso X X') (β : z_iso Z Z')
  : z_iso (X ⊗ Z) (X' ⊗ Z') := (pr1 α,, pr1 β) ,, is_z_iso_binprod_z_iso (pr2 α)(pr2 β).


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

Definition precategory_binproduct_assoc (C0 C1 C2 : category)
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

Definition precategory_binproduct_unassoc (C0 C1 C2 : category)
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

Variable C D E : category.
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

Variable C D E : category.
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

Variable C D E : category.
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

Variable C D E : category.
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

Variable C D E : category.
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

Definition pair_functor_data {A B C D : category}
  (F : A ⟶ C) (G : B ⟶ D) : functor_data (A × B) (C × D).
Proof.
use tpair.
- intro x; apply (make_catbinprod (F (pr1 x)) (G (pr2 x))).
- intros x y f; simpl; apply (catbinprodmor (# F (pr1 f)) (# G (pr2 f))).
Defined.

Definition pair_functor {A B C D : category}
  (F : A ⟶ C) (G : B ⟶ D) : (A × B) ⟶ (C × D).
Proof.
apply (tpair _ (pair_functor_data F G)).
abstract (split;
  [ intro x; simpl; rewrite !functor_id; apply idpath
  | intros x y z f g; simpl; rewrite !functor_comp; apply idpath]).
Defined.

Definition pr1_functor_data (A B : category) :
  functor_data (A × B) A.
Proof.
use tpair.
- intro x; apply (pr1 x).
- intros x y f; simpl; apply (pr1 f).
Defined.

Definition pr1_functor (A B : category) : (A × B) ⟶ A.
Proof.
apply (tpair _ (pr1_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition pr2_functor_data (A B : category) :
  functor_data (A × B) B.
Proof.
use tpair.
- intro x; apply (pr2 x).
- intros x y f; simpl; apply (pr2 f).
Defined.

Definition pr2_functor (A B : category) : (A × B) ⟶ B.
Proof.
apply (tpair _ (pr2_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_functor_data (C : category) :
  functor_data C (C × C).
Proof.
use tpair.
- intro x; apply (make_catbinprod x x).
- intros x y f; simpl; apply (catbinprodmor f f).
Defined.

(* The diagonal functor Δ *)
Definition bindelta_functor (C : category) : C ⟶ (C × C).
Proof.
apply (tpair _ (bindelta_functor_data C)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_pair_functor_data (C D E : category)
  (F : C ⟶ D) (G : C ⟶ E) :
  functor_data C (category_binproduct D E).
Proof.
  use tpair.
  - intro c. apply (make_catbinprod (F c) (G c)).
  - intros x y f. simpl. apply (catbinprodmor (# F f) (# G f)).
Defined.

Lemma is_functor_bindelta_pair_functor_data (C D E : category)
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

Definition bindelta_pair_functor {C D E : category}
  (F : C ⟶ D) (G : C ⟶ E) : C ⟶ (D × E).
Proof.
  apply (tpair _ (bindelta_pair_functor_data C D E F G)).
  apply is_functor_bindelta_pair_functor_data.
Defined.

(** Projections of `bindelta_pair_functor` *)
Definition bindelta_pair_pr1_data
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_trans_data (bindelta_pair_functor F G ∙ pr1_functor _ _) F
  := λ _, identity _.

Definition bindelta_pair_pr1_is_nat_trans
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : is_nat_trans _ _ (bindelta_pair_pr1_data F G).
Proof.
  intros x y f ; cbn ; unfold bindelta_pair_pr1_data.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition bindelta_pair_pr1
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : bindelta_pair_functor F G ∙ pr1_functor _ _ ⟹ F.
Proof.
  use make_nat_trans.
  - exact (bindelta_pair_pr1_data F G).
  - exact (bindelta_pair_pr1_is_nat_trans F G).
Defined.

Definition bindelta_pair_pr1_iso
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_iso
      (bindelta_pair_functor F G ∙ pr1_functor _ _)
      F.
Proof.
  use make_nat_iso.
  - exact (bindelta_pair_pr1 F G).
  - intro.
    apply identity_is_iso.
Defined.

Definition bindelta_pair_pr2_data
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_trans_data (bindelta_pair_functor F G ∙ pr2_functor _ _) G
  := λ _, identity _.

Definition bindelta_pair_pr2_is_nat_trans
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : is_nat_trans _ _ (bindelta_pair_pr2_data F G).
Proof.
  intros x y f ; cbn ; unfold bindelta_pair_pr1_data.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition bindelta_pair_pr2
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : bindelta_pair_functor F G ∙ pr2_functor _ _ ⟹ G.
Proof.
  use make_nat_trans.
  - exact (bindelta_pair_pr2_data F G).
  - exact (bindelta_pair_pr2_is_nat_trans F G).
Defined.

Definition bindelta_pair_pr2_iso
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_iso
      (bindelta_pair_functor F G ∙ pr2_functor _ _)
      G.
Proof.
  use make_nat_iso.
  - exact (bindelta_pair_pr2 F G).
  - intro.
    apply identity_is_iso.
Defined.


(* A swapping functor σ : C × D → D × C. *)
Definition binswap_pair_functor {C D : category} : (C × D) ⟶ (D × C) :=
  bindelta_functor (C × D) ∙ pair_functor (pr2_functor C D) (pr1_functor C D).

(* Reversing the order of three arguments *)
Definition reverse_three_args {C D E : category} : ((C × D) × E) ⟶ ((E × D) × C).
Proof.
  use (functor_composite (precategory_binproduct_unassoc _ _ _)).
  use (functor_composite binswap_pair_functor).
  exact (pair_functor binswap_pair_functor (functor_identity _)).
Defined.

Lemma reverse_three_args_ok {C D E : category} :
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

Definition nat_trans_data_post_whisker_fst_param {B C D P: category}
           {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  nat_trans_data (functor_composite (pair_functor (functor_identity _) G) K)
                 (functor_composite (pair_functor (functor_identity _) H) K) :=
  λ pb : P × B, #K ((identity (ob1 pb),, γ (ob2 pb)):
                      (P × C)⟦ob1 pb,, G(ob2 pb), ob1 pb,, H(ob2 pb)⟧).

Lemma is_nat_trans_post_whisker_fst_param {B C D P: category}
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

Definition post_whisker_fst_param {B C D P: category}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  (functor_composite (pair_functor (functor_identity _) G) K) ⟹
  (functor_composite (pair_functor (functor_identity _) H) K) :=
  make_nat_trans _ _ _ (is_nat_trans_post_whisker_fst_param γ K).


Definition nat_trans_data_post_whisker_snd_param {B C D P: category}
           {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  nat_trans_data (functor_composite (pair_functor G (functor_identity _)) K)
                 (functor_composite (pair_functor H (functor_identity _)) K) :=
  λ bp : B × P, #K ((γ (ob1 bp),, identity (ob2 bp)):
                      (C × P)⟦G(ob1 bp),, ob2 bp, H(ob1 bp),, ob2 bp⟧).

Lemma is_nat_trans_post_whisker_snd_param {B C D P: category}
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

Definition post_whisker_snd_param {B C D P: category}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  (functor_composite (pair_functor G (functor_identity _)) K) ⟹
  (functor_composite (pair_functor H (functor_identity _)) K) :=
  make_nat_trans _ _ _ (is_nat_trans_post_whisker_snd_param γ K).

End whiskering.

Section Currying.
  (** we will "Curry away" the first argument - for our intended use with actions *)

  Context (C D E : category).

Section Def_Curry_Ob.
  Context (F: (C × D) ⟶ E).

  Definition curry_functor_data: functor_data D [C, E].
  Proof.
    use make_functor_data.
    - intro d.
      exact (functor_fix_snd_arg C D E F d).
    - intros d d' f.
      exact (nat_trans_from_functor_fix_snd_morphism_arg C D E F d d' f).
  Defined.

  Lemma curry_functor_data_is_functor: is_functor curry_functor_data.
  Proof.
    split.
    - intro d.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
      etrans.
      { apply maponpaths. apply binprod_id. }
      apply functor_id.
    - intros d1 d2 d3 f g.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
      etrans.
      2: { apply functor_comp. }
      apply maponpaths.
      apply dirprodeq; cbn.
      + apply pathsinv0. apply id_left.
      + apply idpath.
  Qed.

  Definition curry_functor: D ⟶ [C, E] := make_functor curry_functor_data curry_functor_data_is_functor.

End Def_Curry_Ob.

Section Def_Curry_Mor.

  Context {F G: (C × D) ⟶ E} (α: F ⟹ G).

  Definition curry_nattrans : curry_functor F ⟹ curry_functor G.
  Proof.
    use make_nat_trans.
    - intro d.
      exact (nat_trans_fix_snd_arg _ _ _ _ _ α d).
    - intros d d' f.
      apply nat_trans_eq; try exact E.
      intro c.
      cbn.
      unfold nat_trans_from_functor_fix_snd_morphism_arg_data, nat_trans_fix_snd_arg_data.
      apply nat_trans_ax.
  Defined.

End Def_Curry_Mor.


Section Def_Uncurry_Ob.

  Context (G: D ⟶ [C, E]).

  Definition uncurry_functor_data: functor_data (C × D) E.
  Proof.
    use make_functor_data.
    - intro cd. induction cd as [c d].
      exact (pr1 (G d) c).
    - intros cd cd' ff'.
      induction cd as [c d]. induction cd' as [c' d']. induction ff' as [f f'].
      cbn in *.
      exact (#(G d: functor C E) f · pr1 (#G f') c').
  Defined.

  Lemma uncurry_functor_data_is_functor: is_functor uncurry_functor_data.
  Proof.
    split.
    - intro cd. induction cd as [c d].
      cbn.
      rewrite functor_id.
      rewrite id_left.
      assert (H := functor_id G d).
      apply (maponpaths (fun f => pr1 f c)) in H.
      exact H.
    - intros cd1 cd2 cd3 ff' gg'.
      induction cd1 as [c1 d1]. induction cd2 as [c2 d2]. induction cd3 as [c3 d3]. induction ff' as [f f']. induction gg' as [g g'].
      cbn in *.
      rewrite functor_comp.
      assert (H := functor_comp G f' g').
      apply (maponpaths (fun f => pr1 f c3)) in H.
      etrans.
      { apply maponpaths.
        exact H. }
      cbn.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply nat_trans_ax.
  Qed.

  Definition uncurry_functor: (C × D) ⟶ E := make_functor uncurry_functor_data uncurry_functor_data_is_functor.

End Def_Uncurry_Ob.

Section Def_Uncurry_Mor.

  Context {F G: D ⟶ [C, E]} (α: F ⟹ G).

  Definition uncurry_nattrans : uncurry_functor F ⟹ uncurry_functor G.
  Proof.
    use make_nat_trans.
    - intro cd.
      cbn.
      exact (pr1 (α (pr2 cd)) (pr1 cd)).
    - intros cd cd' fg.
      induction cd as [c d]. induction cd' as [c' d']. induction fg as [f g].
      cbn in *.
      assert (aux := nat_trans_ax α d d' g).
      apply (maponpaths pr1) in aux.
      apply toforallpaths in aux.
      assert (auxinst := aux c').
      rewrite <- assoc.
      etrans.
      { apply maponpaths. exact auxinst. }
      clear aux auxinst.
      cbn.
      do 2 rewrite assoc.
      apply cancel_postcomposition.
      apply nat_trans_ax.
  Defined.

End Def_Uncurry_Mor.


Lemma uncurry_after_curry (F: (C × D) ⟶ E): uncurry_functor (curry_functor F) = F.
Proof.
  apply functor_eq. { exact E. }
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  use functor_data_eq.
  - intro cd; apply idpath.
  - cbn. intros cd cd' ff'.
    induction cd as [c d]. induction cd' as [c' d']. induction ff' as [f f'].
    cbn in *.
    unfold functor_fix_snd_arg_mor, nat_trans_from_functor_fix_snd_morphism_arg_data.
    etrans.
    { apply pathsinv0. apply functor_comp. }
    unfold compose. cbn.
    rewrite id_left, id_right.
    apply idpath.
Qed.

Lemma curry_after_uncurry_pointwise (G: D ⟶ [C, E]) (d: D) : pr1 (curry_functor (uncurry_functor G)) d = pr1 G d.
Proof.
  (* UniMath.MoreFoundations.Tactics.show_id_type. *)
  apply functor_eq. { exact E. }
  use functor_data_eq.
  - intro c.
    apply idpath.
  - cbn.
    intros c c' f.
    assert (H := functor_id G d).
    apply (maponpaths (fun f => pr1 f c')) in H.
    etrans.
    { apply maponpaths. exact H. }
    apply id_right.
Qed.

End Currying.


Section Evaluation.
(** functor evaluation is the pointwise counit of the biadjunction behind currying and uncurrying

    for the indended use, we need to switch the order of arguments
*)

  Context {C D : category}.

Definition evaluation_functor: ([C, D] × C) ⟶  D.
Proof.
  apply (functor_composite (@binswap_pair_functor _ _)).
  apply (uncurry_functor).
  exact (functor_identity _).
Defined.

Goal ∏ (F: C ⟶ D) (c: C), evaluation_functor (F ,, c) = F c.
Proof.
  intros.
  apply idpath.
Qed.

End Evaluation.

Section Coevaluation.
  (** for completeness, we also define the pointwise unit of that biadjunction *)

  Context {C D : category}.

  Definition coevaluation_functor: C ⟶  [D, C × D].
  Proof.
    apply curry_functor.
    apply binswap_pair_functor.
  Defined.

End Coevaluation.

Section CategoryBinproductIsoWeq.
  Context {C D : category}
          (x y : category_binproduct C D).

  Definition category_binproduct_iso_map
    : iso (pr1 x) (pr1 y) × iso (pr2 x) (pr2 y) → iso x y.
  Proof.
    intros i.
    simple refine ((pr11 i ,, pr12 i) ,, _).
    apply is_iso_binprod_iso.
    - exact (pr21 i).
    - exact (pr22 i).
  Defined.

  Definition category_binproduct_iso_inv
    : iso x y → iso (pr1 x) (pr1 y) × iso (pr2 x) (pr2 y)
    := λ i, functor_on_iso (pr1_functor C D) i ,, functor_on_iso (pr2_functor C D) i.

  Definition category_binproduct_iso_weq
    : iso (pr1 x) (pr1 y) × iso (pr2 x) (pr2 y) ≃ iso x y.
  Proof.
    use make_weq.
    - exact category_binproduct_iso_map.
    - use gradth.
      + exact category_binproduct_iso_inv.
      + abstract
          (intros i ;
           use pathsdirprod ;
           (use subtypePath ; [ intro ; apply isaprop_is_iso | ]) ;
           apply idpath).
      + abstract
          (intros i ;
           use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
           apply idpath).
  Defined.
End CategoryBinproductIsoWeq.

Section Univalence.
  Context {C D : category}
          (HC : is_univalent C)
          (HD : is_univalent D).

  Definition is_unvialent_category_binproduct
    : is_univalent (category_binproduct C D).
  Proof.
    intros x y.
    use weqhomot.
    - exact (category_binproduct_iso_weq x y
             ∘ weqdirprodf
                 (make_weq _ (HC _ _))
                 (make_weq _ (HD _ _))
             ∘ pathsdirprodweq)%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
         cbn ;
         apply idpath).
  Defined.
End Univalence.

Definition univalent_category_binproduct
           (C₁ C₂ : univalent_category)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (category_binproduct C₁ C₂).
  - use is_unvialent_category_binproduct.
    + exact (pr2 C₁).
    + exact (pr2 C₂).
Defined.
