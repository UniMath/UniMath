
(** Some important constructions on displayed categories

Partial contents:

- Full subcategory as total category of a displayed category
- Displayed category given by a structure on objects and a proposition
   on morphisms of the base category
- Direct products of displayed categories (and their projections)
  - [dirprod_disp_cat D1 D2]
  - [dirprodpr1_disp_functor], [dirprodpr2_disp_functor]
- Sigmas of displayed categories
- Displayed functor cat
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
(* Needed for [functor_lifting]. *)
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Auxiliary.

(* TODO: Move this to another file *)
Lemma isweqcontrprop (X Y : UU) (f : X → Y) :
  iscontr X → isaprop Y → isweq f.
Proof.
  intros HX HY.
  apply isweqimplimpl.
  - intros. apply HX.
  - apply isapropifcontr. apply HX.
  - apply HY.
Defined.

End Auxiliary.

(** * Full subcategories *)

Section full_subcat.

Definition disp_full_sub_ob_mor (C : precategory_ob_mor) (P : C → UU)
  : disp_cat_ob_mor C
  := (P,, (λ a b aa bb f, unit)).

Definition disp_full_sub_id_comp (C : precategory_data) (P : C → UU)
  : disp_cat_id_comp C (disp_full_sub_ob_mor C P).
Proof.
  split; intros; apply tt.
Defined.

Definition disp_full_sub_data (C : precategory_data) (P : C → UU)
  : disp_cat_data C
  :=  disp_full_sub_ob_mor C P,, disp_full_sub_id_comp C P.

Lemma disp_full_sub_locally_prop (C : category) (P : C → UU) :
  locally_propositional (disp_full_sub_data C P).
Proof.
  intro; intros; apply isapropunit.
Qed.

Definition disp_full_sub (C : category) (P : C → UU)
  : disp_cat C.
Proof.
  use make_disp_cat_locally_prop.
  - exact (disp_full_sub_data C P).
  - apply disp_full_sub_locally_prop.
Defined.

Lemma disp_full_sub_univalent (C : category) (P : C → UU) :
  (∏ x : C, isaprop (P x)) →
  is_univalent_disp (disp_full_sub C P).
Proof.
  intro HP.
  apply is_univalent_disp_from_fibers.
  intros x xx xx'. cbn in *.
  apply isweqcontrprop. apply HP.
  apply isofhleveltotal2.
  - apply isapropunit.
  - intro. apply (@isaprop_is_z_iso_disp _ (disp_full_sub C P)).
Defined.

Definition full_subcat (C : category) (P : C → UU) : category := total_category (disp_full_sub C P).

Definition is_univalent_full_subcat (C : category) (univC : is_univalent C) (P : C → UU) :
  (∏ x : C, isaprop (P x)) → is_univalent (full_subcat C P).
Proof.
  intro H.
  apply is_univalent_total_category.
  - exact univC.
  - exact (disp_full_sub_univalent _ _ H).
Defined.

End full_subcat.

(** * Displayed category from structure on objects and compatibility on morphisms *)

Section struct_hom.

Variable C : category.
(* Variable univC : is_univalent C. *)
Variable P : ob C -> UU.
(* Variable Pisset : ∏ x, isaset (P x). *)
Variable H : ∏ (x y : C), P x → P y → C⟦x,y⟧ → UU.
Arguments H {_ _} _ _ _ .
Variable Hisprop : ∏ x y a b (f : C⟦x,y⟧), isaprop (H a b f).
Variable Hid : ∏ (x : C) (a : P x), H a a (identity _ ).
Variable Hcomp : ∏ (x y z : C) a b c (f : C⟦x,y⟧) (g : C⟦y,z⟧),
                 H a b f → H b c g → H a c (f · g).

Definition disp_struct_ob_mor : disp_cat_ob_mor C.
Proof.
  exists P.
  intros ? ? f a b; exact (H f a b ).
Defined.

Definition disp_struct_id_comp : disp_cat_id_comp _ disp_struct_ob_mor.
Proof.
  split; cbn; intros.
  - apply Hid.
  - eapply Hcomp. apply X. apply X0.
Qed.

Definition disp_struct_data : disp_cat_data C := _ ,, disp_struct_id_comp.

Definition disp_struct : disp_cat C.
Proof.
  use make_disp_cat_locally_prop.
  - exact disp_struct_data.
  - intro; intros; apply Hisprop.
Defined.

End struct_hom.

(** * Products of displayed (pre)categories

We directly define direct products of displayed categories over a base.

An alternative would be to define the direct product as the [sigma_disp_cat] of the pullback to either factor.  *)

Definition dirprod_disp_cat_ob_mor
           {C : precategory_ob_mor} (D1 D2 : disp_cat_ob_mor C)
  : disp_cat_ob_mor C.
Proof.
  exists (λ c, D1 c × D2 c).
  intros x y xx yy f.
  exact (pr1 xx -->[f] pr1 yy × pr2 xx -->[f] pr2 yy).
Defined.

Definition dirprod_disp_cat_id_comp
           {C : precategory_data}
           (D1 D2 : disp_cat_data C)
  : disp_cat_id_comp _ (dirprod_disp_cat_ob_mor D1 D2).
Proof.
  apply tpair.
  - intros x (x1, x2).
    exact (id_disp x1,, id_disp x2).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition dirprod_disp_cat_data
           {C : precategory_data}
           (D1 D2 : disp_cat_data C)
  : disp_cat_data C
  := (_ ,, dirprod_disp_cat_id_comp D1 D2).

Section Dirprod.

Context {C : category} (D1 D2 : disp_cat C).

Definition dirprod_disp_cat_axioms
  : disp_cat_axioms _ (dirprod_disp_cat_data D1 D2).
Proof.
  repeat apply make_dirprod.
  - intros. apply dirprod_paths; use (id_left_disp _ @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
  - intros. apply dirprod_paths; use (id_right_disp _ @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
  - intros. apply dirprod_paths; use (assoc_disp _ _ _ @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
  - intros. apply isaset_dirprod; apply homsets_disp.
Qed.

Definition dirprod_disp_cat : disp_cat C
  := (_ ,, dirprod_disp_cat_axioms).

(** ** Characterization of the isomorphisms of the direct product of displayed categories *)
(** TODO: generalize over an aritrary base isomorphism *)
Definition z_iso_disp_prod1
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) (xx1,, xx2) (xx1',, xx2') →
  (z_iso_disp (identity_z_iso x) xx1 xx1') × (z_iso_disp (identity_z_iso x) xx2 xx2').
Proof.
  unfold z_iso_disp. cbn.
  intros [[f1 f2] Hff].
  destruct Hff as [[g1 g2] Hfg].
  cbn in Hfg. destruct Hfg as [Hgf Hfg].
  use tpair.
  - exists f1, g1.
    split.
    + etrans. apply (maponpaths dirprod_pr1 Hgf).
      apply pr1_transportf.
    + etrans. apply (maponpaths dirprod_pr1 Hfg).
      apply pr1_transportf.
  - exists f2, g2.
    split.
    + etrans. apply (maponpaths dirprod_pr2 Hgf).
      apply pr2_transportf.
    + etrans. apply (maponpaths dirprod_pr2 Hfg).
      apply pr2_transportf.
Defined.

Definition z_iso_disp_prod2
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  (z_iso_disp (identity_z_iso x) xx1 xx1') × (z_iso_disp (identity_z_iso x) xx2 xx2') →
  @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) (xx1,, xx2) (xx1',, xx2').
Proof.
  unfold z_iso_disp. cbn.
  intros [[f1 Hf1] [f2 Hf2]].
  destruct Hf1 as [g1 [Hgf1 Hfg1]].
  destruct Hf2 as [g2 [Hgf2 Hfg2]].
  exists (f1,,f2), (g1,,g2).
  split.
  - apply dirprod_paths.
    + etrans. apply Hgf1.
      apply pathsinv0. apply pr1_transportf.
    + etrans. apply Hgf2.
      apply pathsinv0. apply pr2_transportf.
  - apply dirprod_paths.
    + etrans. apply Hfg1.
      apply pathsinv0. apply pr1_transportf.
    + etrans. apply Hfg2.
      apply pathsinv0. apply pr2_transportf.
Defined.

Lemma z_iso_disp_prod21
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x)
      i
:
  z_iso_disp_prod2 xx1 xx1' xx2 xx2' (z_iso_disp_prod1 xx1 xx1' xx2 xx2' i) = i.
Proof.
  apply eq_z_iso_disp. cbn. reflexivity.
Qed.

Lemma z_iso_disp_prod12
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x)
      (t : z_iso_disp (identity_z_iso x) xx1 xx1' × z_iso_disp (identity_z_iso x) xx2 xx2')
:
  z_iso_disp_prod1 xx1 xx1' xx2 xx2' (z_iso_disp_prod2 xx1 xx1' xx2 xx2' t) = t.
Proof.
  apply dirprod_paths.
  - apply eq_z_iso_disp. cbn. reflexivity.
  - apply eq_z_iso_disp. cbn. reflexivity.
Qed.

Lemma z_iso_disp_prod_weq
      (x : C)
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) (xx1,, xx2) (xx1',, xx2') ≃
  (z_iso_disp (identity_z_iso x) xx1 xx1') × (z_iso_disp (identity_z_iso x) xx2 xx2').
Proof.
  exists (z_iso_disp_prod1 xx1 xx1' xx2 xx2').
  use isweq_iso.
  - apply z_iso_disp_prod2.
  - apply z_iso_disp_prod21.
  - apply z_iso_disp_prod12.
Defined.

Lemma z_iso_disp_aux_weq
      (U1 : is_univalent_in_fibers D1)
      (U2 : is_univalent_in_fibers D2)
      (x : C)
      (xx xx' : D1 x × D2 x)

:
  xx = xx'
    ≃ @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) xx xx'.
Proof.
  eapply weqcomp. apply pathsdirprodweq.
  apply invweq. eapply weqcomp. apply z_iso_disp_prod_weq.
  apply invweq.
  apply weqdirprodf.
  - exists idtoiso_fiber_disp. apply U1.
  - exists idtoiso_fiber_disp. apply U2.
Defined.

Lemma dirprod_disp_cat_is_univalent :
  is_univalent_disp D1 →
  is_univalent_disp D2 →
  is_univalent_disp dirprod_disp_cat.
Proof.
  intros HD1 HD2.
  apply is_univalent_disp_from_fibers.
  intros x xx xx'.
  use isweqhomot.
  - apply z_iso_disp_aux_weq.
    + apply is_univalent_in_fibers_from_univalent_disp.
      apply HD1.
    + apply is_univalent_in_fibers_from_univalent_disp.
      apply HD2.
  - intros p. induction p. cbn.
    apply (@eq_z_iso_disp _ dirprod_disp_cat).
    reflexivity.
  - apply z_iso_disp_aux_weq.
Defined.

Definition dirprodpr1_disp_functor_data
  : disp_functor_data (functor_identity C) dirprod_disp_cat (D1).
Proof.
  use tpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition dirprodpr1_disp_functor_axioms
  : disp_functor_axioms dirprodpr1_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr1_disp_functor
  : disp_functor (functor_identity C) dirprod_disp_cat (D1)
:= (dirprodpr1_disp_functor_data,, dirprodpr1_disp_functor_axioms).


Definition dirprodpr2_disp_functor_data
  : disp_functor_data (functor_identity C) dirprod_disp_cat (D2).
Proof.
  use tpair.
  - intros x xx; exact (pr2 xx).
  - intros x y xx yy f ff; exact (pr2 ff).
Defined.

Definition dirprodpr2_disp_functor_axioms
  : disp_functor_axioms dirprodpr2_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr2_disp_functor
  : disp_functor (functor_identity C) dirprod_disp_cat (D2)
:= (dirprodpr2_disp_functor_data,, dirprodpr2_disp_functor_axioms).

End Dirprod.

Declare Scope disp_cat_scope.
Notation "D1 × D2" := (dirprod_disp_cat D1 D2) : disp_cat_scope.
Delimit Scope disp_cat_scope with disp_cat.
Bind Scope disp_cat_scope with disp_cat.

(** ** Functors into displayed categories *)

(** Just like how context morphisms in a CwA can be built up out of terms, similarly, the basic building-block for functors into (total cats of) displayed categories will be analogous to a term.

We call it a _section_ (though we define it intrinsically, not as a section in a (bi)category), since it corresponds to a section of the forgetful functor. *)

Section Sections.

  Definition section_disp_data {C} (D : disp_cat C) : UU
    := ∑ (Fob : forall x:C, D x),
      (forall (x y:C) (f:x --> y), Fob x -->[f] Fob y).

  Definition section_disp_on_objects {C} {D : disp_cat C}
             (F : section_disp_data D) (x : C)
    := pr1 F x : D x.

  Coercion section_disp_on_objects : section_disp_data >-> Funclass.

  Definition section_disp_on_morphisms {C} {D : disp_cat C}
             (F : section_disp_data D) {x y : C} (f : x --> y)
    := pr2 F _ _ f : F x -->[f] F y.

  Notation "# F" := (section_disp_on_morphisms F)
                      (at level 3) : mor_disp_scope.

  Definition section_disp_axioms {C} {D : disp_cat C}
             (F : section_disp_data D) : UU
    := ((forall x:C, # F (identity x) = id_disp (F x))
          × (forall (x y z : C) (f : x --> y) (g : y --> z),
                # F (f · g) = (# F f) ;; (# F g))).

  Definition section_disp {C} (D : disp_cat C) : UU
    := total2 (@section_disp_axioms C D).

  Definition section_disp_data_from_section_disp {C} {D : disp_cat C}
             (F : section_disp D) := pr1 F.

  Coercion section_disp_data_from_section_disp
    : section_disp >-> section_disp_data.

  Definition section_disp_id {C} {D : disp_cat C} (F : section_disp D)
    := pr1 (pr2 F).

  Definition section_disp_comp {C} {D : disp_cat C} (F : section_disp D)
    := pr2 (pr2 F).

End Sections.

(** With sections defined, we can now define _lifts_ to a displayed category of a functor into the base. *)
Section Functor_Lifting.

  Notation "# F" := (section_disp_on_morphisms F)
                      (at level 3) : mor_disp_scope.

  Definition functor_lifting
             {C C' : category} (D : disp_cat C) (F : functor C' C)
    := section_disp (reindex_disp_cat F D).

  Identity Coercion section_from_functor_lifting
    : functor_lifting >-> section_disp.

  (** Note: perhaps it would be better to define [functor_lifting] directly?
  Reindexed displayed-cats are a bit confusing to work in, since a term like [id_disp xx] is ambiguous: it can mean both the identity in the original displayed category, or the identity in the reindexing, which is nearly but not quite the same.  This shows up already in the proofs of [lifted_functor_axioms] below. *)

  Definition lifted_functor_data {C C' : category} {D : disp_cat C}
             {F : functor C' C} (FF : functor_lifting D F)
    : functor_data C' (total_category D).
  Proof.
    exists (λ x, (F x ,, FF x)).
    intros x y f. exists (# F f)%cat. exact (# FF f).
  Defined.

  Definition lifted_functor_axioms {C C' : category} {D : disp_cat C}
             {F : functor C' C} (FF : functor_lifting D F)
    : is_functor (lifted_functor_data FF).
  Proof.
    split.
    - intros x. use total2_paths_f; simpl.
      apply functor_id.
      eapply pathscomp0. apply maponpaths, (section_disp_id FF).
      cbn. apply transportfbinv.
    - intros x y z f g. use total2_paths_f; simpl.
      apply functor_comp.
      eapply pathscomp0. apply maponpaths, (section_disp_comp FF).
      cbn. apply transportfbinv.
  Qed.

  Definition lifted_functor {C C' : category} {D : disp_cat C}
             {F : functor C' C} (FF : functor_lifting D F)
    : functor C' (total_category D)
    := (_ ,, lifted_functor_axioms FF).

  Lemma from_lifted_functor {C C' : category} {D : disp_cat C}
        {F : functor C' C} (FF : functor_lifting D F):
    functor_composite (lifted_functor FF) (pr1_category D) = F.
  Proof.
    use (functor_eq _ _ (homset_property C)). apply idpath.
  Qed.

  (** redo the development for the special case that F is the identity *)
  Definition section_functor_data {C : category} {D : disp_cat C} (sd : section_disp D)
    : functor_data C (total_category D).
  Proof.
    exists (λ x, (x ,, sd x)).
    intros x y f. exists f. exact (section_disp_on_morphisms sd f).
  Defined.

  Definition section_functor_axioms {C : category} {D : disp_cat C} (sd : section_disp D)
    : is_functor (section_functor_data sd).
  Proof.
    split.
    - intro x. use total2_paths_f; simpl.
      + apply idpath.
      + apply (section_disp_id sd).
    - intros x y z f g. use total2_paths_f; simpl.
      + apply idpath.
      + apply (section_disp_comp sd).
  Qed.

  Definition section_functor {C : category} {D : disp_cat C} (sd : section_disp D):
    functor C (total_category D) :=
    section_functor_data sd,, section_functor_axioms sd.

  Lemma from_section_functor {C : category} {D : disp_cat C} (sd : section_disp D):
    functor_composite (section_functor sd) (pr1_category D) = functor_identity C.
  Proof.
    use (functor_eq _ _ (homset_property C)). apply idpath.
  Qed.

End Functor_Lifting.

(* Natural transformations of sections  *)
Section Section_transformation.

Definition section_nat_trans_disp_data
    {C : category}
    {D : disp_cat C}
    (F F' : section_disp D) : UU :=
  ∏ (x : C), F x -->[identity _] F' x.

Definition section_nat_trans_disp_axioms
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp_data F F') : UU :=
  ∏ x x' (f : x --> x'),
      transportf _
      (id_right _ @ !(id_left _))
      (section_disp_on_morphisms F f ;; nt x') =
    nt x ;; section_disp_on_morphisms F' f.

Lemma isaprop_section_nat_trans_disp_axioms
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp_data F F') :
  isaprop (section_nat_trans_disp_axioms nt).
Proof.
  do 3 (apply impred; intro).
  apply homsets_disp.
Qed.

Definition section_nat_trans_disp
    {C : category}
    {D : disp_cat C}
    (F F': section_disp D) : UU :=
  ∑ (nt : section_nat_trans_disp_data F F'), section_nat_trans_disp_axioms nt.

Definition section_nt_disp_data_from_section_nt_disp
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : section_nat_trans_disp_data F F'
  := pr1 nt.

Definition section_nat_trans_data_from_section_nat_trans_disp_funclass
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
  ∏ x : ob C, F x -->[identity _]  F' x := section_nt_disp_data_from_section_nt_disp nt.
Coercion section_nat_trans_data_from_section_nat_trans_disp_funclass :
    section_nat_trans_disp >-> Funclass.

Definition section_nt_disp_axioms_from_section_nt_disp
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : section_nat_trans_disp_axioms nt
  := pr2 nt.

Definition section_nat_trans_data
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
      nat_trans_data (section_functor F) (section_functor F').
Proof.
  intro x.
  exists (identity _).
  exact (nt x).
Defined.

Definition section_nat_trans_axioms
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
      is_nat_trans (section_functor F) (section_functor F') (section_nat_trans_data nt).
Proof.
  intros x x' f.
  use total2_paths_f.
  - simpl. now rewrite id_left, id_right.
  - simpl.
    rewrite <- (section_nt_disp_axioms_from_section_nt_disp nt).
    apply transportf_paths.
    apply homset_property.
Qed.

Definition section_nat_trans
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : nat_trans (section_functor F) (section_functor F') :=
  section_nat_trans_data nt,, section_nat_trans_axioms nt.

Definition section_nat_trans_id
    {C : category}
    {D : disp_cat C}
    (F : section_disp D)
    : section_nat_trans_disp F F.
Proof.
  use tpair.
  - intro.
    exact (id_disp _).
  - simpl.
    intros x x' f.

    rewrite id_left_disp, id_right_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
Defined.

Definition section_nat_trans_comp
    {C : category}
    {D : disp_cat C}
    {F F' F'': section_disp D}
    (FF' : section_nat_trans_disp F F')
    (F'F'' : section_nat_trans_disp F' F'') :
  section_nat_trans_disp F F''.
Proof.
  use tpair.
  - intro x.
    exact (transportf _ (id_left _) (FF' x ;; F'F'' x)).
  - simpl.
    intros x x' f.

    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.

    rewrite assoc_disp_var, transport_f_f.
    rewrite <- (section_nt_disp_axioms_from_section_nt_disp F'F'').

    rewrite mor_disp_transportf_prewhisker, transport_f_f.

    do 2 rewrite assoc_disp, transport_f_b.
    rewrite <- (section_nt_disp_axioms_from_section_nt_disp FF').

    rewrite mor_disp_transportf_postwhisker, transport_f_f.

    apply maponpaths_2.
    apply homset_property.
Defined.

Lemma section_nat_trans_eq {C : category} {D : disp_cat C}
  (F F' : section_disp D) (a a' : section_nat_trans_disp F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { now apply funextsec. }
  apply (total2_paths_f H').
  apply proofirrelevance.
  apply isaprop_section_nat_trans_disp_axioms.
Qed.

Definition section_nat_trans_id_left
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (FF' : section_nat_trans_disp F F') :
  section_nat_trans_comp (section_nat_trans_id F) FF' = FF'.
Proof.
  use section_nat_trans_eq.
  intro x.
  simpl.
  rewrite id_left_disp.
  rewrite transport_f_b.
  apply transportf_set.
  apply homset_property.
Qed.

Definition section_nat_trans_id_right
    {C : category}
    {D : disp_cat C}
    {F F': section_disp D}
    (FF' : section_nat_trans_disp F F') :
  section_nat_trans_comp FF' (section_nat_trans_id F') = FF'.
Proof.
  use section_nat_trans_eq.
  intro x.
  simpl.
  rewrite id_right_disp.
  rewrite transport_f_b.
  apply transportf_set.
  apply homset_property.
Qed.

Definition section_nat_trans_assoc
    {C : category}
    {D : disp_cat C}
    {F1 F2 F3 F4: section_disp D}
    (F12 : section_nat_trans_disp F1 F2)
    (F23 : section_nat_trans_disp F2 F3)
    (F34 : section_nat_trans_disp F3 F4) :
  section_nat_trans_comp F12 (section_nat_trans_comp F23 F34) = section_nat_trans_comp (section_nat_trans_comp F12 F23) F34.
Proof.
  use section_nat_trans_eq.
  intro x.
  simpl.
  rewrite mor_disp_transportf_postwhisker.
  rewrite mor_disp_transportf_prewhisker.
  do 2 rewrite transport_f_f.
  rewrite assoc_disp.
  rewrite transport_f_b.
  apply maponpaths_2.
  apply homset_property.
Qed.

End Section_transformation.

(** * Displayed functor category

Displayed functors and natural transformations form a displayed category over the ordinary functor category between the bases. *)

Section Functor.
(* TODO: clean up this section a bit. *)

Variables C' C : category.
Variable D' : disp_cat C'.
Variable D : disp_cat C.

Let FunctorsC'C := functor_category C' C.


Definition disp_functor_cat :
  disp_cat (FunctorsC'C).
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * intro F.
        apply (disp_functor F D' D).
      * simpl. intros F' F FF' FF a.
        apply (disp_nat_trans a FF' FF).
    + use tpair.
      * intros x xx.
        apply disp_nat_trans_id.
      * intros ? ? ? ? ? ? ? ? X X0. apply (disp_nat_trans_comp X X0 ).
  - repeat split.
    + apply disp_nat_trans_id_left.
    + apply disp_nat_trans_id_right.
    + apply disp_nat_trans_assoc.
    + intros ; apply isaset_disp_nat_trans.
Defined.

(** TODO : characterize isos in the displayed functor cat *)

(** TODO: integrate [has_homsets] assumptions below! *)
Definition pointwise_z_iso_from_nat_z_iso {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : z_iso F G) (a : A) : z_iso (pr1 F a) (pr1 G a)
  :=
  functor_z_iso_pointwise_if_z_iso _ _ _ _ _ b (pr2 b)_ .


Definition pointwise_inv_is_inv_on_z_iso {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : z_iso F G) (a : A) :

  inv_from_z_iso (pointwise_z_iso_from_nat_z_iso b a) =
                                       pr1 (inv_from_z_iso b) a.
Proof.
  apply idpath.
Defined.

(** TODO : write a few lemmas about isos in
    the disp functor precat,
    to make the following sane

    However: it seems to be better to work on
    https://github.com/UniMath/UniMath/issues/362
    first.
*)

Definition is_pointwise_z_iso_if_is_disp_functor_cat_z_iso
  (x y : FunctorsC'C)
  (f : z_iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : is_z_iso_disp f FF)
  :
  forall x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                          (pr1 FF _ xx' ).
Proof.
  intros x' xx'.
  use tpair.
  - set (X:= pr1 H). simpl in X.
    apply (transportb _ (pointwise_inv_is_inv_on_z_iso f _ ) (X x' xx')).
  - simpl. repeat split.
    + etrans. apply mor_disp_transportf_postwhisker.
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= pr1 (pr2 H)).
      assert (XRT :=  (maponpaths pr1 XR)).
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'.
      clear XRT' XRT XR.
      assert (XR := @disp_nat_trans_transportf C' C D' D).
      specialize (XR _ _ _ _ (! z_iso_after_z_iso_inv f)).
      etrans. apply XR.
      apply maponpaths_2, homset_property.
    + etrans. apply mor_disp_transportf_prewhisker.
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= inv_mor_after_z_iso_disp H).
      assert (XRT :=  (maponpaths pr1 XR)).
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'.
      clear XRT' XRT XR.
      assert (XR := @disp_nat_trans_transportf C' C D' D).
      specialize (XR _ _ _ _ (! z_iso_inv_after_z_iso f)).
      etrans. apply XR.
      apply maponpaths_2, homset_property.
Defined.

(* The following part has holes because of the migration from [iso] to [z_iso] as notion of isomorphism.
   It compiled at the moment of commenting it. But at the price of two "Admitted".

Lemma is_disp_nat_trans_pointwise_inv
  (x y : FunctorsC'C)
  (f : z_iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f] yy)
  (H : ∏ (x' : C') (xx' : D' x'),
      is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f x') (pr1 FF x' xx'))
  (x' x0 : C')
  (f0 : x' --> x0)
  (xx' : D' x')
  (xx0 : D' x0)
  (ff : xx' -->[ f0] xx0)
  : # (pr1 yy) ff ;; pr1 (H x0 xx0) =
  transportb (mor_disp (pr1 yy x' xx') (pr1 xx x0 xx0)) (nat_trans_ax (inv_from_z_iso f) x' x0 f0)
    (pr1 (H x' xx') ;; # (pr1 xx) ff).
Proof.
  show_id_type.
Admitted.

Definition inv_disp_from_pointwise_z_iso
  (x y : FunctorsC'C)
  (f : z_iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : forall x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                          (pr1 FF _ xx' ))
  :
       yy -->[ inv_from_z_iso f] xx.
Proof.
  use tpair.
  + intros x' xx'.
    simpl in xx. simpl in yy.
    apply (pr1 (H x' xx')).
  + intros x' x0 f0 xx' xx0 ff.
    apply is_disp_nat_trans_pointwise_inv.
Defined.

Definition is_disp_functor_cat_iso_if_pointwise_z_iso
  (x y : FunctorsC'C)
  (f : z_iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : forall x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                          (pr1 FF _ xx' ))
  : is_z_iso_disp f FF.
Proof.
  use tpair.
  - apply (inv_disp_from_pointwise_z_iso _ _ _ _ _ FF H).
  - split.
    + apply subtypePath.
      { intro. apply isaprop_disp_nat_trans_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply disp_nat_trans_transportf.
      cbn.
      apply pathsinv0.
      admit.
      (*
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths. apply (iso_disp_after_inv_mor (H c' xx')).
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
*)
    + apply subtypePath.
      { intro. apply isaprop_disp_nat_trans_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply disp_nat_trans_transportf.
      cbn.
      apply pathsinv0.
      admit.
      (* etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths. apply (inv_mor_after_iso_disp (H c' xx')).
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property. *)
Admitted.

Definition is_disp_functor_cat_z_iso_iff_pointwise_z_iso
  (x y : FunctorsC'C)
  (f : z_iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  :
  (∏ x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                          (pr1 FF _ xx' ))
    <->
    is_z_iso_disp f FF.
Proof.
  split.
  - apply is_disp_functor_cat_iso_if_pointwise_z_iso.
  - apply is_pointwise_z_iso_if_is_disp_functor_cat_z_iso.
Defined.

*)
End Functor.
