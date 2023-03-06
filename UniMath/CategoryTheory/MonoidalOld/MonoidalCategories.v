(**
  Monoidal categories

  Based on an implementation by Anthony Bordg.

  Behaviour w.r.t. to swapped tensor product added by Ralph Matthes in 2019
  Isos replaced by z_isos in 2021
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
Notation "( c , d )" := (make_catbinprod c d).
Notation "( f #, g )" := (catbinprodmor f g).

Section Monoidal_Precat.

Context {C : category} (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Lemma tensor_id {X Y : C} : id X #⊗ id Y = id (X ⊗ Y).
Proof.
  apply (functor_id tensor).
Qed.

Lemma tensor_comp {X Y Z X' Y' Z' : C} (f : X --> Y) (g : Y --> Z) (f' : X' --> Y') (g' : Y' --> Z') :
  (f · g) #⊗ (f' · g') = f #⊗ f' · g #⊗ g'.
Proof.
  rewrite binprod_comp.
  apply (functor_comp tensor).
Qed.

Definition is_z_iso_tensor_z_iso {X Y X' Y' : C} {f : X --> Y} {g : X' --> Y'}
           (f_is_z_iso : is_z_isomorphism f) (g_is_z_iso : is_z_isomorphism g) : is_z_isomorphism (f #⊗ g).
Proof.
  exact (functor_on_is_z_isomorphism _ (is_z_iso_binprod_z_iso f_is_z_iso g_is_z_iso)).
Defined.

(* I ⊗ - *)
Definition I_pretensor : C ⟶ C := functor_fix_fst_arg _ _ _ tensor I.

Lemma I_pretensor_ok: functor_on_objects I_pretensor = λ c, I ⊗ c.
Proof.
  apply idpath.
Qed.

(* λ *)
Definition left_unitor : UU :=
  nat_z_iso I_pretensor (functor_identity C).

Definition left_unitor_funclass (λ' : left_unitor):
  ∏ x : ob C, I_pretensor x -->  x
  := pr1 (nat_z_iso_to_trans λ').
Coercion left_unitor_funclass : left_unitor >-> Funclass.

Definition left_unitor_to_nat_trans (λ' : left_unitor): nat_trans I_pretensor (functor_identity C)
  := nat_z_iso_to_trans λ'.
Coercion left_unitor_to_nat_trans: left_unitor >-> nat_trans.

(* - ⊗ I *)
Definition I_posttensor : C ⟶ C := functor_fix_snd_arg _ _ _ tensor I.

Lemma I_posttensor_ok: functor_on_objects I_posttensor = λ c, c ⊗ I.
Proof.
  apply idpath.
Qed.

(* ρ *)
Definition right_unitor : UU :=
  nat_z_iso I_posttensor (functor_identity C).

Definition right_unitor_funclass (ρ' : right_unitor):
  ∏ x : ob C, I_posttensor x -->  x
  := pr1 (nat_z_iso_to_trans ρ').
Coercion right_unitor_funclass : right_unitor >-> Funclass.

Definition right_unitor_to_nat_trans (ρ' : right_unitor): nat_trans I_posttensor (functor_identity C)
  := nat_z_iso_to_trans ρ'.
Coercion right_unitor_to_nat_trans: right_unitor >-> nat_trans.

(* (- ⊗ =) ⊗ ≡ *)
Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite (pair_functor tensor (functor_identity _)) tensor.

Lemma assoc_left_ok: functor_on_objects assoc_left =
  λ c, (ob1 (ob1 c) ⊗ ob2 (ob1 c)) ⊗ ob2 c.
Proof.
  apply idpath.
Qed.

(* - ⊗ (= ⊗ ≡) *)
Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite
    (precategory_binproduct_unassoc _ _ _)
    (functor_composite (pair_functor (functor_identity _) tensor) tensor).

Lemma assoc_right_ok: functor_on_objects assoc_right =
  λ c, ob1 (ob1 c) ⊗ (ob2 (ob1 c) ⊗ ob2 c).
Proof.
  apply idpath.
Qed.

(* α *)
Definition associator : UU :=
  nat_z_iso assoc_left assoc_right.
(* This definition goes in the opposite direction of that by Mac Lane (CWM 2nd ed., p.162)
   but conforms to the def. on Wikipedia. *)

Definition associator_funclass (α' : associator):
  ∏ x : ob ((C ⊠ C) ⊠ C), assoc_left x -->  assoc_right x
  := pr1 (nat_z_iso_to_trans α').
Coercion associator_funclass : associator >-> Funclass.

Definition associator_to_nat_trans (α' : associator): nat_trans assoc_left assoc_right
  := nat_z_iso_to_trans α'.
Coercion associator_to_nat_trans: associator >-> nat_trans.

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  ∏ (a b : C), pr1 ρ' a #⊗ id b = pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) =
   pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).

Definition is_strict (eq_λ : I_pretensor = functor_identity C) (λ' : left_unitor)
           (eq_ρ : I_posttensor = functor_identity C) (ρ' : right_unitor)
           (eq_α : assoc_left = assoc_right) (α' : associator) : UU :=
  (is_nat_z_iso_id eq_λ λ') × (is_nat_z_iso_id eq_ρ ρ') × (is_nat_z_iso_id eq_α α').

End Monoidal_Precat.

Definition monoidal_cat : UU :=
  ∑ C : category, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
         (triangle_eq tensor I λ' ρ' α') × (pentagon_eq tensor α').

(*
Definition monoidal_precat_struct : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor, unit.

Definition make_monoidal_precat_struct (C: precategory)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor): monoidal_precat_struct :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, tt)))))).
*)

Definition make_monoidal_cat (C: category)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor)
  (eq1: triangle_eq tensor I λ' ρ' α')(eq2: pentagon_eq tensor α'): monoidal_cat :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, (eq1,, eq2))))))).

Definition monoidal_cat_cat (M : monoidal_cat) : category := pr1 M.
Coercion monoidal_cat_cat : monoidal_cat >-> category.

Section Monoidal_Cat_Accessors.

  Context (M : monoidal_cat).

  (** it is important that no new coercions are used in the given types in the following projections *)

Definition monoidal_cat_tensor : pr1 M ⊠ pr1 M ⟶ pr1 M := pr1 (pr2 M).

Definition monoidal_cat_unit : pr1 M := pr1 (pr2 (pr2 M)).

Definition monoidal_cat_left_unitor : left_unitor (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_cat_right_unitor : right_unitor (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_cat_associator : associator (pr1 (pr2 M)) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

Definition monoidal_cat_triangle_eq : triangle_eq (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) (pr1 (pr2 (pr2 (pr2 M)))) (pr1 (pr2 (pr2 (pr2 (pr2 M))))) (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))).

Definition monoidal_cat_pentagon_eq : pentagon_eq (pr1 (pr2 M)) (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))) := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))).

End Monoidal_Cat_Accessors.


Definition strict_monoidal_cat : UU :=
  ∑ M : monoidal_cat,
  ∏ (eq_λ : I_pretensor (monoidal_cat_tensor M) (monoidal_cat_unit M) =
  functor_identity (pr1 M)),
  ∏ (eq_ρ : I_posttensor (monoidal_cat_tensor M) (monoidal_cat_unit M) =
  functor_identity (pr1 M)),
  ∏ (eq_α : assoc_left (monoidal_cat_tensor M) =
  assoc_right (monoidal_cat_tensor M)),
  is_strict (monoidal_cat_tensor M) (monoidal_cat_unit M) eq_λ (monoidal_cat_left_unitor M) eq_ρ (monoidal_cat_right_unitor M) eq_α (monoidal_cat_associator M).

Section swapped_tensor.

Context (M : monoidal_cat).

Definition swapping_of_tensor: M ⊠ M ⟶ M := functor_composite binswap_pair_functor (monoidal_cat_tensor M).

Definition associator_swapping_of_tensor: associator swapping_of_tensor.
Proof.
  set (α := monoidal_cat_associator M).
  set (α' := nat_z_iso_to_trans_inv α).
  red.
  set (trafo := (pre_whisker reverse_three_args α'): (assoc_left swapping_of_tensor) ⟹ (assoc_right swapping_of_tensor)).
  assert (tisziso: is_nat_z_iso trafo).
  { red. intro c. set (aux := pr2 (nat_z_iso_inv α)).
    apply (pre_whisker_on_nat_z_iso reverse_three_args α' aux).
  }
  exact (trafo,, tisziso).
Defined.

Lemma triangle_eq_swapping_of_tensor: triangle_eq swapping_of_tensor (monoidal_cat_unit M)
  (monoidal_cat_right_unitor M) (monoidal_cat_left_unitor M) associator_swapping_of_tensor.
Proof.
  red. intros a b. cbn.
  set (H := monoidal_cat_triangle_eq M).
  unfold triangle_eq in H.
  etrans.
  2: { apply cancel_precomposition.
       apply pathsinv0.
       apply H. }
  clear H.
  rewrite assoc.
  etrans.
  { apply pathsinv0.
    apply id_left. }
  apply cancel_postcomposition.
  apply pathsinv0.
  set (f := nat_z_iso_pointwise_z_iso (monoidal_cat_associator M)((b, monoidal_cat_unit M), a)).
  apply (z_iso_after_z_iso_inv f).
Qed.

Lemma pentagon_eq_swapping_of_tensor: pentagon_eq swapping_of_tensor associator_swapping_of_tensor.
Proof.
  red. intros a b c d. cbn.
  set (H := monoidal_cat_pentagon_eq M).
  unfold pentagon_eq in H.
  set (f := nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((d, c), monoidal_cat_tensor M (b, a))).
  apply (z_iso_inv_on_right _ _ _ f).
  apply pathsinv0.
  set (f' := nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((monoidal_cat_tensor M (d, c), b), a)).
  apply (inv_z_iso_unique' _ _ _ f').
  unfold precomp_with.
  rewrite assoc.
  etrans.
  { apply cancel_postcomposition.
    apply H. }
  clear H.
  repeat rewrite assoc.
  etrans.
  { do 2 apply cancel_postcomposition.
    rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    apply (functor_comp (functor_fix_fst_arg _ _ _ (monoidal_cat_tensor M) d)).
  }
  etrans.
  { do 2 apply cancel_postcomposition.
    apply cancel_precomposition.
    apply maponpaths.
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((c, b), a))). }
  rewrite functor_id.
  rewrite id_right.
  etrans.
  { apply cancel_postcomposition.
    rewrite <- assoc.
    apply cancel_precomposition.
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((d, monoidal_cat_tensor M (c, b)), a))). }
  rewrite id_right.
  etrans.
  apply pathsinv0.
  apply (functor_comp (functor_fix_snd_arg _ _ _ (monoidal_cat_tensor M) a)).
  etrans.
  { apply maponpaths.
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((d, c), b))). }
  cbn.
  unfold functor_fix_snd_arg_mor.
  use functor_id.
Qed.

Definition swapping_of_monoidal_cat: monoidal_cat.
Proof.
  use (make_monoidal_cat M swapping_of_tensor).
  - exact (monoidal_cat_unit M).
  - apply monoidal_cat_right_unitor.
  - apply monoidal_cat_left_unitor.
  - exact associator_swapping_of_tensor.
  - exact triangle_eq_swapping_of_tensor.
  - exact pentagon_eq_swapping_of_tensor.
Defined.

End swapped_tensor.

Section coherence_lemmas.

Context {Mon_V : monoidal_cat}.

Let I        : Mon_V                  := monoidal_cat_unit Mon_V.
Let tensor   : Mon_V ⊠ Mon_V ⟶ Mon_V := monoidal_cat_tensor Mon_V.
Let α        : associator tensor      := monoidal_cat_associator Mon_V.
Let l_unitor : left_unitor tensor I   := monoidal_cat_left_unitor Mon_V.
Let r_unitor : right_unitor tensor I  := monoidal_cat_right_unitor Mon_V.

Local Notation "X ⊗ Y" := (tensor (X, Y)).
Local Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Lemma tensor_comp_left {X Y Z W : Mon_V} (f : X --> Y) (g : Y --> Z) : ((f · g) #⊗ id W) = (f #⊗ id W) · (g #⊗ id W).
Proof.
  rewrite <- (functor_comp tensor).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  apply idpath.
Defined.

Lemma tensor_comp_right {X Y Z W : Mon_V} (f : X --> Y) (g : Y --> Z) : (id W #⊗ (f · g)) = (id W #⊗ f) · (id W #⊗ g).
Proof.
  rewrite <- (functor_comp tensor).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  apply idpath.
Defined.

Lemma I_posttensor_faithful {X Y : Mon_V} {f g : X --> Y} : (f #⊗ id I) = (g #⊗ id I) -> f = g.
Proof.
  intro H.
  apply (pre_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 r_unitor _))).
  use (pathscomp0 (! (nat_trans_ax r_unitor _ _ f))).
  use (pathscomp0 _ (nat_trans_ax r_unitor _ _ g)).
  apply cancel_postcomposition.
  assumption.
Defined.

Lemma I_pretensor_faithful {X Y : Mon_V} {f g : X --> Y} : (id I #⊗ f) = (id I #⊗ g) -> f = g.
Proof.
  intro H.
  apply (pre_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 l_unitor _))).
  use (pathscomp0 (! (nat_trans_ax l_unitor _ _ f))).
  use (pathscomp0 _ (nat_trans_ax l_unitor _ _ g)).
  apply cancel_postcomposition.
  assumption.
Defined.

(*
  The following three lemmas are from [Kelly, 1964].
  https://doi.org/10.1016/0021-8693(64)90018-3
  monoidal_cat_triangle_eq <-> diagram (6) in [Kelly, 1964]
  monoidal_cat_pentagon_eq <-> diagram (1)
  right_unitor_of_tensor <-> diagram (7)
  left_unitor_right_unitor_of_unit <-> diagram (4)
  left_unitor_of_tensor <-> diagram (5)
*)
Lemma right_unitor_of_tensor (X Y : Mon_V) : r_unitor (X ⊗ Y) = α ((X, Y), I) · (id X #⊗ r_unitor Y).
Proof.
  apply I_posttensor_faithful.
  rewrite tensor_comp_left.
  apply (post_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 α (_, _)))).
  rewrite assoc'.
  apply (transportb (λ h, _ = _ · h) (nat_trans_ax α _ _ ((_#, _)#, _))).
  simpl.
  rewrite assoc.
  apply (transportb (λ h, _ = _ · #tensor (id _ #, h)) (monoidal_cat_triangle_eq Mon_V _ _)).
  apply (transportf (λ k, _ = _ · #tensor (k #, _)) (id_left (id X))).
  change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite (functor_comp tensor).
  apply (transportb (λ h, h · _ = _) (monoidal_cat_triangle_eq Mon_V _ _)).
  apply (transportf (λ h, _ · #tensor (h #, _) · _ = _) (functor_id tensor (X, Y))).
  rewrite assoc'.
  apply (transportb (λ h, _ · h = _) (nat_trans_ax α _ _ ((_#, _)#, _))).
  rewrite !assoc.
  apply cancel_postcomposition.
  apply monoidal_cat_pentagon_eq.
Defined.

Lemma left_unitor_right_unitor_of_unit : l_unitor I = r_unitor I.
Proof.
  apply I_pretensor_faithful.
  apply (pre_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 α ((_, _), _)))).
  apply (pathscomp0 (! (monoidal_cat_triangle_eq Mon_V I I))).
  use (pathscomp0 _ (right_unitor_of_tensor I I)).
  apply (post_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 r_unitor _))).
  apply (nat_trans_ax r_unitor).
Defined.

Lemma left_unitor_of_tensor (X Y : Mon_V) : α ((I, X), Y) · l_unitor (X ⊗ Y) = l_unitor X #⊗ id Y.
Proof.
  apply I_pretensor_faithful.
  rewrite tensor_comp_right.
  apply (pre_comp_with_z_iso_is_inj (pr2 α ((I, (I ⊗ X)), Y))).
  use (pathscomp0 _ (nat_trans_ax α _ _ ((_ #, _) #, _))).
  simpl.
  apply (pre_comp_with_z_iso_is_inj (functor_on_is_z_isomorphism (functor_fix_snd_arg _ _ _ tensor Y) (pr2 α ((I, I), X)))).
  simpl.
  unfold functor_fix_snd_arg_mor.
  change (make_dirprod ?x ?y) with (x #, y).
  rewrite !assoc.
  apply (transportf (λ h, _ = h · _) (functor_comp tensor _ _)).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  apply (transportf (λ h, h · _ = _) (monoidal_cat_pentagon_eq Mon_V I I X Y)).
  rewrite assoc'.
  apply (transportf (λ h, _ · h = _) (monoidal_cat_triangle_eq Mon_V _ _)).
  simpl.
  apply (transportf (λ h, _ · #tensor (_ #, h) = _) (functor_id tensor (X, Y))).
  apply (pathscomp0 (! (nat_trans_ax α _ _ ((_ #, _) #, _)))).
  simpl.
  apply cancel_postcomposition.
  apply pathsinv0.
  apply maponpaths.
  apply dirprod_paths; simpl; [|apply id_left].
  apply pathsinv0.
  apply monoidal_cat_triangle_eq.
Defined.

(* Corollaries for the inverses of left and right unitors. *)

Lemma tensor_z_isomorphism_left : ∏ (x y z : Mon_V) (f : x --> y) (f_z_iso : is_z_isomorphism f), # tensor (is_z_isomorphism_mor f_z_iso #, id z) = is_z_isomorphism_mor (functor_on_is_z_isomorphism (functor_fix_snd_arg _ _ _ tensor z) f_z_iso).
Proof.
  intros.
  reflexivity.
Qed.

Lemma tensor_z_isomorphism_right : ∏ (x y z : Mon_V) (f : x --> y) (f_z_iso : is_z_isomorphism f), # tensor (id z #, is_z_isomorphism_mor f_z_iso) = is_z_isomorphism_mor (functor_on_is_z_isomorphism (functor_fix_fst_arg _ _ _ tensor z) f_z_iso).
Proof.
  intros.
  reflexivity.
Qed.

Lemma monoidal_cat_triangle_eq_inv (X Y : Mon_V) : (nat_z_iso_to_trans_inv r_unitor X #⊗ id Y) · α ((X, I), Y) = (id X #⊗ nat_z_iso_to_trans_inv l_unitor Y).
Proof.
  cbn.
  rewrite (tensor_z_isomorphism_right _ _ _ _ _ : #tensor _ = _).
  rewrite (tensor_z_isomorphism_left _ _ _ _ _ : #tensor _ = _).
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply monoidal_cat_triangle_eq.
Qed.

Corollary left_unitor_inv_right_unitor_inv_of_unit : nat_z_iso_to_trans_inv l_unitor I = nat_z_iso_to_trans_inv r_unitor _.
Proof.
  apply (post_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 l_unitor _))).
  apply (pathscomp0 (is_inverse_in_precat2 (is_z_isomorphism_is_inverse_in_precat (pr2 l_unitor _)))).
  apply (transportb (λ f, id _ = is_z_isomorphism_mor _ · f) left_unitor_right_unitor_of_unit).
  apply pathsinv0.
  apply (is_inverse_in_precat2 (is_z_isomorphism_is_inverse_in_precat (pr2 r_unitor _))).
Qed.

Corollary left_unitor_inv_of_tensor (X Y : Mon_V) : (nat_z_iso_to_trans_inv l_unitor _ #⊗ id _) · α ((_, _), _) = nat_z_iso_to_trans_inv l_unitor (X ⊗ Y).
Proof.
  simpl.
  rewrite tensor_z_isomorphism_left.
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply pathsinv0.
  apply left_unitor_of_tensor.
Qed.

Corollary right_unitor_inv_of_tensor (X Y : Mon_V) : (id _ #⊗ nat_z_iso_to_trans_inv r_unitor _) = nat_z_iso_to_trans_inv r_unitor (X ⊗ Y)  · α ((_, _), _).
Proof.
  simpl.
  rewrite tensor_z_isomorphism_right.
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply pathsinv0.
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply right_unitor_of_tensor.
Qed.

End coherence_lemmas.

(** Accessors and notations for monoidal categories *)
Declare Scope moncat.
Local Open Scope moncat.

Definition monoidal_cat_tensor_pt
           {V : monoidal_cat}
           (x y : V)
  : V
  := monoidal_cat_tensor V (x ,, y).

Notation "x ⊗ y" :=  (monoidal_cat_tensor _ (x ,, y)) : moncat.

Definition monoidal_cat_tensor_mor
           {V : monoidal_cat}
           {x₁ x₂ y₁ y₂ : V}
           (f : x₁ --> x₂)
           (g : y₁ --> y₂)
  : x₁ ⊗ y₁ --> x₂ ⊗ y₂
  := # (monoidal_cat_tensor V) (f #, g).

Notation "f #⊗ g" := (monoidal_cat_tensor_mor f g) (at level 31) : moncat.

Notation "𝟙" := (monoidal_cat_unit _) : moncat. (* \b1 *)

Section MonoidalCatAccessors.
  Context {V : monoidal_cat}.

  Definition tensor_id_id
             (x y : V)
    : identity x #⊗ identity y = identity (x ⊗ y).
  Proof.
    apply tensor_id.
  Qed.

  Definition tensor_comp_mor
             {x₁ x₂ x₃ y₁ y₂ y₃ : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : (f · f') #⊗ (g · g') = f #⊗ g · f' #⊗ g'.
  Proof.
    apply tensor_comp.
  Qed.

  Definition tensor_comp_id_l
             {x y₁ y₂ y₃ : V}
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : (identity x) #⊗ (g · g') = (identity x) #⊗ g · (identity x) #⊗ g'.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_l_id_l
             {x₁ x₂ y₁ y₂ y₃ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : f #⊗ (g · g') = (identity _) #⊗ g · f #⊗ g'.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_l_id_r
             {x₁ x₂ y₁ y₂ y₃ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂) (g' : y₂ --> y₃)
    : f #⊗ (g · g') = f #⊗ g · (identity _) #⊗ g'.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition tensor_comp_id_r
             {x₁ x₂ x₃ y : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
    : (f · f') #⊗ (identity y) = f #⊗ (identity y) · f' #⊗ (identity y).
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_r_id_l
             {x₁ x₂ x₃ y₁ y₂ : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
             (g : y₁ --> y₂)
    : (f · f') #⊗ g = f #⊗ (identity _) · f' #⊗ g.
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition tensor_comp_r_id_r
             {x₁ x₂ x₃ y₁ y₂ : V}
             (f : x₁ --> x₂) (f' : x₂ --> x₃)
             (g : y₁ --> y₂)
    : (f · f') #⊗ g = f #⊗ g · f' #⊗ (identity _).
  Proof.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition tensor_split
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : f #⊗ g = identity _ #⊗ g · f #⊗ identity _.
  Proof.
    refine (_ @ tensor_comp_mor _ _ _ _).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Definition tensor_split'
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : f #⊗ g = f #⊗ identity _ · identity _ #⊗ g.
  Proof.
    refine (_ @ tensor_comp_mor _ _ _ _).
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Definition tensor_swap
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : f #⊗ identity _ · identity _ #⊗ g = identity _ #⊗ g · f #⊗ identity _.
  Proof.
    rewrite <- tensor_split, <- tensor_split'.
    apply idpath.
  Qed.

  Definition tensor_swap'
             {x₁ x₂ y₁ y₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : identity _ #⊗ g · f #⊗ identity _ = f #⊗ identity _ · identity _ #⊗ g.
  Proof.
    rewrite <- tensor_split, <- tensor_split'.
    apply idpath.
  Qed.

  Definition mon_lunitor
             (x : V)
    : 𝟙 ⊗ x --> x
    := monoidal_cat_left_unitor V x.

  Definition tensor_lunitor
             {x y : V}
             (f : x --> y)
    : identity _ #⊗ f · mon_lunitor y
      =
      mon_lunitor x · f.
  Proof.
    exact (nat_trans_ax (monoidal_cat_left_unitor V) x y f).
  Qed.

  Definition mon_linvunitor
             (x : V)
    : x --> 𝟙 ⊗ x
    := nat_z_iso_inv (monoidal_cat_left_unitor V) x.

  Definition tensor_linvunitor
             {x y : V}
             (f : x --> y)
    : f · mon_linvunitor y
      =
      mon_linvunitor x · identity _ #⊗ f.
  Proof.
    exact (nat_trans_ax (nat_z_iso_inv (monoidal_cat_left_unitor V)) x y f).
  Qed.

  Definition mon_lunitor_linvunitor
             (x : V)
    : mon_lunitor x · mon_linvunitor x = identity _.
  Proof.
    cbn.
    exact (z_iso_inv_after_z_iso (_ ,, pr2 (monoidal_cat_left_unitor V) x)).
  Qed.

  Definition mon_linvunitor_lunitor
             (x : V)
    : mon_linvunitor x · mon_lunitor x = identity _.
  Proof.
    cbn.
    exact (z_iso_after_z_iso_inv (_ ,, pr2 (monoidal_cat_left_unitor V) x)).
  Qed.

  Definition mon_runitor
             (x : V)
    : x ⊗ 𝟙 --> x
    := monoidal_cat_right_unitor V x.

  Definition tensor_runitor
             {x y : V}
             (f : x --> y)
    : f #⊗ identity _ · mon_runitor y
      =
      mon_runitor x · f.
  Proof.
    exact (nat_trans_ax (monoidal_cat_right_unitor V) x y f).
  Qed.

  Definition mon_rinvunitor
             (x : V)
    : x --> x ⊗ 𝟙
    := nat_z_iso_inv (monoidal_cat_right_unitor V) x.

  Definition tensor_rinvunitor
             {x y : V}
             (f : x --> y)
    : f · mon_rinvunitor y
      =
      mon_rinvunitor x · f #⊗ identity _.
  Proof.
    exact (nat_trans_ax (nat_z_iso_inv (monoidal_cat_right_unitor V)) x y f).
  Qed.

  Definition mon_runitor_rinvunitor
             (x : V)
    : mon_runitor x · mon_rinvunitor x = identity _.
  Proof.
    cbn.
    exact (z_iso_inv_after_z_iso (_ ,, pr2 (monoidal_cat_right_unitor V) x)).
  Qed.

  Definition mon_rinvunitor_runitor
             (x : V)
    : mon_rinvunitor x · mon_runitor x = identity _.
  Proof.
    cbn.
    exact (z_iso_after_z_iso_inv (_ ,, pr2 (monoidal_cat_right_unitor V) x)).
  Qed.

  Definition mon_lassociator
             (x y z : V)
    : (x ⊗ y) ⊗ z --> x ⊗ (y ⊗ z)
    := monoidal_cat_associator V ((x ,, y) ,, z).

  Definition tensor_lassociator
             {x₁ x₂ y₁ y₂ z₁ z₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
             (h : z₁ --> z₂)
    : (f #⊗ g) #⊗ h · mon_lassociator _ _ _
      =
      mon_lassociator _ _ _ · f #⊗ (g #⊗ h).
  Proof.
    exact (nat_trans_ax
             (monoidal_cat_associator V)
             ((x₁ ,, y₁) ,, z₁) ((x₂ ,, y₂) ,, z₂)
             ((f ,, g) ,, h)).
  Qed.

  Definition mon_rassociator
             (x y z : V)
    : x ⊗ (y ⊗ z) --> (x ⊗ y) ⊗ z
    := nat_z_iso_inv (monoidal_cat_associator V) ((x ,, y) ,, z).

  Definition tensor_rassociator
             {x₁ x₂ y₁ y₂ z₁ z₂ : V}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
             (h : z₁ --> z₂)
    : f #⊗ (g #⊗ h) · mon_rassociator _ _ _
      =
      mon_rassociator _ _ _ · (f #⊗ g) #⊗ h.
  Proof.
    exact (nat_trans_ax
             (nat_z_iso_inv (monoidal_cat_associator V))
             ((x₁ ,, y₁) ,, z₁) ((x₂ ,, y₂) ,, z₂)
             ((f ,, g) ,, h)).
  Qed.

  Definition mon_lassociator_rassociator
             (x y z : V)
    : mon_lassociator x y z · mon_rassociator x y z = identity _.
  Proof.
    cbn.
    exact (z_iso_inv_after_z_iso
             (_ ,, pr2 (monoidal_cat_associator V)
                ((x ,, y) ,, z))).
  Qed.

  Definition mon_rassociator_lassociator
             (x y z : V)
    : mon_rassociator x y z · mon_lassociator x y z = identity _.
  Proof.
    cbn.
    exact (z_iso_after_z_iso_inv
             (_ ,, pr2 (monoidal_cat_associator V)
                ((x ,, y) ,, z))).
  Qed.

  Definition mon_triangle
             (x y : V)
    : mon_runitor x #⊗ identity y
      =
      mon_lassociator x 𝟙 y · (identity x #⊗ mon_lunitor y).
  Proof.
    exact (monoidal_cat_triangle_eq V x y).
  Qed.

  Definition mon_inv_triangle
             (x y : V)
    : identity x #⊗ mon_linvunitor y
      =
      mon_rinvunitor x #⊗ identity y · mon_lassociator x 𝟙 y.
  Proof.
    refine (!_).
    use (z_iso_inv_on_right
           _ _ _
           (functor_on_z_iso
              (monoidal_cat_tensor V)
              (precatbinprod_z_iso
                 (nat_z_iso_pointwise_z_iso (monoidal_cat_right_unitor V) x)
                 (identity_z_iso y)))).
    use (z_iso_inv_on_left
           _ _ _ _
           (functor_on_z_iso
              (monoidal_cat_tensor V)
              (precatbinprod_z_iso
                 (identity_z_iso x)
                 (nat_z_iso_pointwise_z_iso (monoidal_cat_left_unitor V) y)))).
    exact (mon_triangle x y).
  Qed.

  Definition mon_lunitor_triangle
             (x y : V)
    : mon_lassociator 𝟙 x y · mon_lunitor (x ⊗ y)
      =
      mon_lunitor x #⊗ identity y.
  Proof.
    exact (left_unitor_of_tensor x y).
  Qed.

  Definition mon_linvunitor_triangle
             (x y : V)
    : mon_linvunitor x #⊗ identity y · mon_lassociator 𝟙 x y
      =
      mon_linvunitor (x ⊗ y).
  Proof.
    exact (left_unitor_inv_of_tensor x y).
  Qed.

  Definition mon_runitor_triangle
             (x y : V)
    : mon_rassociator x y 𝟙 · mon_runitor (x ⊗ y)
      =
      identity x #⊗ mon_runitor y.
  Proof.
    etrans.
    {
      apply maponpaths.
      apply right_unitor_of_tensor.
    }
    rewrite !assoc.
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      apply mon_rassociator_lassociator.
    }
    apply id_left.
  Qed.

  Definition mon_rinvunitor_triangle
             (x y : V)
    : identity x #⊗ mon_rinvunitor y · mon_rassociator x y 𝟙
      =
      mon_rinvunitor (x ⊗ y).
  Proof.
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      exact (right_unitor_inv_of_tensor x y).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply mon_lassociator_rassociator.
    }
    apply id_right.
  Qed.

  Definition mon_runitor_I_mon_lunitor_I
    : mon_runitor 𝟙 = mon_lunitor 𝟙.
  Proof.
    refine (!_).
    exact left_unitor_right_unitor_of_unit.
  Qed.

  Definition mon_lunitor_I_mon_runitor_I
    : mon_lunitor 𝟙 = mon_runitor 𝟙.
  Proof.
    rewrite mon_runitor_I_mon_lunitor_I.
    apply idpath.
  Qed.

  Definition mon_rinvunitor_I_mon_linvunitor_I
    : mon_rinvunitor 𝟙 = mon_linvunitor 𝟙.
  Proof.
    cbn.
    refine (_ @ id_left _).
    use (z_iso_inv_on_left _ _ _ _ (_ ,, pr2 (monoidal_cat_left_unitor V) 𝟙)).
    cbn.
    refine (!_).
    use (z_iso_inv_on_right _ _ _ (_ ,, pr2 (monoidal_cat_right_unitor V) 𝟙)).
    cbn.
    rewrite id_right.
    exact mon_lunitor_I_mon_runitor_I.
  Qed.

  Definition mon_linvunitor_I_mon_rinvunitor_I
    : mon_linvunitor 𝟙 = mon_rinvunitor 𝟙.
  Proof.
    rewrite mon_rinvunitor_I_mon_linvunitor_I.
    apply idpath.
  Qed.
End MonoidalCatAccessors.
