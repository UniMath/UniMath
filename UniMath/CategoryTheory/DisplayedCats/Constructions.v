
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
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
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

Definition disp_full_sub_axioms (C : category) (P : C → UU)
  : disp_cat_axioms _ (disp_full_sub_data C P).
Proof.
  repeat split; intros; try (apply proofirrelevance; apply isapropunit).
  apply isasetaprop; apply isapropunit.
Qed.

Definition disp_full_sub (C : category) (P : C → UU)
  : disp_cat C := _ ,, disp_full_sub_axioms C P.

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
  - intros ?. apply (@isaprop_is_iso_disp _ (disp_full_sub C P)).
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

Definition disp_struct_axioms : disp_cat_axioms _ disp_struct_data.
Proof.
  repeat split; intros; try (apply proofirrelevance; apply Hisprop).
  apply isasetaprop; apply Hisprop.
Qed.

Definition disp_struct : disp_cat C := _ ,, disp_struct_axioms.

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
Definition iso_disp_prod1
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  @iso_disp _ dirprod_disp_cat _ _ (identity_iso x) (xx1,, xx2) (xx1',, xx2') →
  (iso_disp (identity_iso x) xx1 xx1') × (iso_disp (identity_iso x) xx2 xx2').
Proof.
  unfold iso_disp. cbn.
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

Definition iso_disp_prod2
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  (iso_disp (identity_iso x) xx1 xx1') × (iso_disp (identity_iso x) xx2 xx2') →
  @iso_disp _ dirprod_disp_cat _ _ (identity_iso x) (xx1,, xx2) (xx1',, xx2').
Proof.
  unfold iso_disp. cbn.
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

Lemma iso_disp_prod21
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x)
      i
:
  iso_disp_prod2 xx1 xx1' xx2 xx2' (iso_disp_prod1 xx1 xx1' xx2 xx2' i) = i.
Proof.
  apply eq_iso_disp. cbn. reflexivity.
Qed.

Lemma iso_disp_prod12
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x)
      (t : iso_disp (identity_iso x) xx1 xx1' × iso_disp (identity_iso x) xx2 xx2')
:
  iso_disp_prod1 xx1 xx1' xx2 xx2' (iso_disp_prod2 xx1 xx1' xx2 xx2' t) = t.
Proof.
  apply dirprod_paths.
  - apply eq_iso_disp. cbn. reflexivity.
  - apply eq_iso_disp. cbn. reflexivity.
Qed.

Lemma iso_disp_prod_weq
      (x : C)
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  @iso_disp _ dirprod_disp_cat _ _ (identity_iso x) (xx1,, xx2) (xx1',, xx2') ≃
  (iso_disp (identity_iso x) xx1 xx1') × (iso_disp (identity_iso x) xx2 xx2').
Proof.
  exists (iso_disp_prod1 xx1 xx1' xx2 xx2').
  use gradth.
  - apply iso_disp_prod2.
  - apply iso_disp_prod21.
  - apply iso_disp_prod12.
Defined.

Lemma iso_disp_aux_weq
      (U1 : is_univalent_in_fibers D1)
      (U2 : is_univalent_in_fibers D2)
      (x : C)
      (xx xx' : D1 x × D2 x)

:
  xx = xx'
    ≃ @iso_disp _ dirprod_disp_cat _ _ (identity_iso x) xx xx'.
Proof.
  eapply weqcomp. apply pathsdirprodweq.
  apply invweq. eapply weqcomp. apply iso_disp_prod_weq.
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
  - apply iso_disp_aux_weq.
    + apply is_univalent_in_fibers_from_univalent_disp.
      apply HD1.
    + apply is_univalent_in_fibers_from_univalent_disp.
      apply HD2.
  - intros p. induction p. cbn.
    apply (@eq_iso_disp _ dirprod_disp_cat).
    reflexivity.
  - apply iso_disp_aux_weq.
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

(** * Sigmas of displayed (pre)categories *)
Section Sigma.

Context {C : category}
        {D : disp_cat C}
        (E : disp_cat (total_category D)).

Definition sigma_disp_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, ∑ (d : D c), (E (c,,d))).
  intros x y xx yy f.
  exact (∑ (fD : pr1 xx -->[f] pr1 yy),
                (pr2 xx -->[f,,fD] pr2 yy)).
Defined.

Definition sigma_disp_cat_id_comp
  : disp_cat_id_comp _ sigma_disp_cat_ob_mor.
Proof.
  apply tpair.
  - intros x xx.
    exists (id_disp _). exact (id_disp (pr2 xx)).
  - intros x y z f g xx yy zz ff gg.
    exists (pr1 ff ;; pr1 gg). exact (pr2 ff ;; pr2 gg).
Defined.

Definition sigma_disp_cat_data : disp_cat_data C
  := (_ ,, sigma_disp_cat_id_comp).


Definition sigma_disp_cat_axioms
  : disp_cat_axioms _ sigma_disp_cat_data.
Proof.
  repeat apply tpair.
  - intros. use total2_reassoc_paths'.
    + apply id_left_disp.
    + etrans. exact (id_left_disp (pr2 ff)).
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply id_right_disp.
    + etrans. exact (id_right_disp (pr2 ff)).
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply assoc_disp.
    + etrans.
        exact (assoc_disp (pr2 ff) (pr2 gg) (pr2 hh)).
      apply maponpaths_2, homset_property.
  - intros. apply isaset_total2; intros; apply homsets_disp.
Qed.

Definition sigma_disp_cat : disp_cat C
  := (_ ,, sigma_disp_cat_axioms).

Definition sigmapr1_disp_functor_data
  : disp_functor_data (functor_identity C) sigma_disp_cat D.
Proof.
  use tpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition sigmapr1_disp_functor_axioms
  : disp_functor_axioms sigmapr1_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition sigmapr1_disp_functor
  : disp_functor (functor_identity C) sigma_disp_cat D
:= (sigmapr1_disp_functor_data,, sigmapr1_disp_functor_axioms).

(* TODO: complete [sigmapr2_disp]; will be a [functor_lifting], not a [disp_functor]. *)

(** ** Transport and isomorphism lemmas *)

Lemma pr1_transportf_sigma_disp {x y : C} {f f' : x --> y} (e : f = f')
    {xxx : sigma_disp_cat x} {yyy} (fff : xxx -->[f] yyy)
  : pr1 (transportf _ e fff) = transportf _ e (pr1 fff).
Proof.
  destruct e; apply idpath.
Qed.

Lemma pr2_transportf_sigma_disp {x y : C} {f f' : x --> y} (e : f = f')
    {xxx : sigma_disp_cat x} {yyy} (fff : xxx -->[f] yyy)
  : pr2 (transportf _ e fff)
  = transportf (λ ff, pr2 xxx -->[ff] _ ) (two_arg_paths_f (*total2_paths2*) e (! pr1_transportf_sigma_disp e fff))
      (pr2 fff).
Proof.
  destruct e. apply pathsinv0.
  etrans. apply maponpaths_2, maponpaths, maponpaths.
  apply (homsets_disp _ _ _ _ _ _ (idpath _)).
  apply idpath.
Qed.


(** ** Univalence *)

Local Open Scope hide_transport_scope.

Definition is_iso_sigma_disp_aux1
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : iso x y} (fff : xxx -->[f] yyy)
    (ii : is_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_iso_disp (@total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  : yyy -->[inv_from_iso f] xxx.
Proof.
  exists (inv_mor_disp_from_iso ii).
  set (ggg := inv_mor_disp_from_iso iii).
  exact (transportf _ (inv_mor_total_iso _ _) ggg).
Defined.

Lemma is_iso_sigma_disp_aux2
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : iso x y} (fff : xxx -->[f] yyy)
    (ii : is_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_iso_disp (@total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  :   (is_iso_sigma_disp_aux1 fff ii iii) ;; fff
    = transportb _ (iso_after_iso_inv f) (id_disp yyy)
  ×
      fff ;; (is_iso_sigma_disp_aux1 fff ii iii)
    = transportb _ (iso_inv_after_iso f) (id_disp xxx).
Proof.
  split.
  - use total2_paths_f.
    + abstract ( etrans;
        [ apply iso_disp_after_inv_mor
        | apply pathsinv0, pr1_transportf_sigma_disp]).
    + etrans. 2: apply @pathsinv0, pr2_transportf_sigma_disp.
      etrans. apply maponpaths.
        use (mor_disp_transportf_postwhisker
          (@inv_mor_total_iso _ _ (_,,_) (_,,_) f ffi) _ (pr2 fff)).
      etrans. apply functtransportf.
      etrans. apply transport_f_f.
      etrans. eapply transportf_bind.
        apply (iso_disp_after_inv_mor iii).
      apply maponpaths_2, (@homset_property (total_category D)).
  - use total2_paths_f; cbn.
    + abstract ( etrans;
        [ apply inv_mor_after_iso_disp
        | apply pathsinv0, pr1_transportf_sigma_disp ]).
    + etrans. 2: apply @pathsinv0, pr2_transportf_sigma_disp.
      etrans. apply maponpaths.
      use (mor_disp_transportf_prewhisker
        (@inv_mor_total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff) _).
      etrans. apply functtransportf.
      etrans. apply transport_f_f.
      etrans. eapply transportf_bind.
        apply (inv_mor_after_iso_disp iii).
      apply maponpaths_2, (@homset_property (total_category D)).
Qed.

Lemma is_iso_sigma_disp
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : iso x y} (fff : xxx -->[f] yyy)
    (ii : is_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_iso_disp (@total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  : is_iso_disp f fff.
Proof.
  exists (is_iso_sigma_disp_aux1 fff ii iii).
  apply is_iso_sigma_disp_aux2.
Defined.

Definition sigma_disp_iso
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    {f : iso x y} (ff : iso_disp f (pr1 xx) (pr1 yy))
    (fff : iso_disp (@total_iso _ _ (_,,_) (_,,_) f ff) (pr2 xx) (pr2 yy))
  : iso_disp f xx yy.
Proof.
  exists (pr1 ff,, pr1 fff). use is_iso_sigma_disp; cbn.
  - exact (pr2 ff).
  - exact (pr2 fff).
Defined.

Definition sigma_disp_iso_map
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : iso x y)
  : (∑ ff : iso_disp f (pr1 xx) (pr1 yy),
       iso_disp (@total_iso _ _ (_,,_) (_,,_) f ff) (pr2 xx) (pr2 yy))
  -> iso_disp f xx yy
:= λ ff, sigma_disp_iso _ _ (pr1 ff) (pr2 ff).

Lemma sigma_disp_isweq_iso
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : iso x y)
  : isweq (sigma_disp_iso_map xx yy f).
Proof.
Abort.

(*
Definition sigma_disp_iso_equiv
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : iso x y)
:= make_weq _ (sigma_disp_isweq_iso xx yy f).
*)

(*
Lemma is_univalent_sigma_disp (DD : is_univalent_disp D) (EE : is_univalent_disp E)
  : is_univalent_disp sigma_disp_cat.
Proof.
  apply is_univalent_disp_from_fibers.
  intros x xx yy.
  use weqhomot.
  - destruct xx as [xx xxx], yy as [yy yyy].
     use (@weqcomp _ (∑ ee : xx = yy, transportf (λ r, E (x,,r)) ee xxx = yyy) _ _ _).
      refine (total2_paths_equiv _ _ _).
    set (i := fun (ee : xx = yy) => (total2_paths2 (idpath _) ee)).
    apply @weqcomp with
        (∑ ee : xx = yy, transportf _ (i ee) xxx = yyy).
      apply weqfibtototal; intros ee.
      refine (_ ,, isweqpathscomp0l _ _).
      (* TODO: a pure transport lemma; maybe break out? *)
      destruct ee; apply idpath.
    apply @weqcomp with (∑ ee : xx = yy,
             iso_disp (@idtoiso (total_category _) (_,,_) (_,,_) (i ee)) xxx yyy).
      apply weqfibtototal; intros ee.
      exists (fun (eee : transportf _ (i ee) xxx = yyy) => idtoiso_disp _ eee).
      apply EE.
    apply @weqcomp with (∑ ee : xx = yy, iso_disp
         (@total_iso _ D (_,,_) (_,,_) _ (idtoiso_disp (idpath _) ee)) xxx yyy).
      apply weqfibtototal; intros ee.
      use tpair.
        refine (transportf (λ I, iso_disp I xxx yyy) _).
        unfold i.
      (* TODO: maybe break out this lemma on [idtoiso]? *)
      (* Note: [abstract] here is to speed up a [cbn] below. *)
        destruct ee. abstract (apply eq_iso, idpath).
      exact (isweqtransportf (λ I, iso_disp I xxx yyy) _).
    apply (@weqcomp _ (∑ f : iso_disp (identity_iso x) xx yy,
                      (iso_disp (@total_iso _ D (_,,_) (_,,_) _ f) xxx yyy)) _).
      refine (weqfp (make_weq _ _) _). refine (DD _ _ (idpath _) _ _).
    apply (sigma_disp_iso_equiv (_,,_) (_,,_) _).
  - assert (lemma2 : forall i i' (e : i = i') ii,
                 pr1 (transportf (λ i, iso_disp i (pr2 xx) (pr2 yy)) e ii)
                 = transportf _ (maponpaths pr1 e) (pr1 ii)).
      intros; destruct e; apply idpath.
    intros ee; apply eq_iso_disp.
    destruct ee, xx as [xx xxx]; cbn.
    apply maponpaths.
    etrans. cbn in lemma2.
    (* This [match] is to supply the 3rd argument of [lemma2], without referring to the identifier auto-generated by [abstract] above. *)
    match goal with |[ |- pr1 (transportf _ ?H _) = _ ]
      => apply (lemma2 _ _ H _) end.
    refine (@maponpaths_2 _ _ _ _ _ (idpath _) _ _).
    etrans. use maponpaths. apply eq_iso, idpath.
      apply isaset_iso, homset_property.
   apply (@homset_property (total_category _) (_,,_) (_,,_)).
Qed.
*)

End Sigma.

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
    + apply isaset_disp_nat_trans.
Defined.

(** TODO : characterize isos in the displayed functor cat *)

(** TODO: integrate [has_homsets] assumptions below! *)
Definition pointwise_iso_from_nat_iso {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) : iso (pr1 F a) (pr1 G a)
  :=
  functor_iso_pointwise_if_iso _ _ _ _ _ b (pr2 b)_ .


Definition pointwise_inv_is_inv_on {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) :

  inv_from_iso (pointwise_iso_from_nat_iso b a) =
                                       pr1 (inv_from_iso b) a.
Proof.
  apply id_right.
Defined.

(** TODO : write a few lemmas about isos in
    the disp functor precat,
    to make the following sane

    However: it seems to be better to work on
    https://github.com/UniMath/UniMath/issues/362
    first.
*)

Definition is_pointwise_iso_if_is_disp_functor_cat_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : is_iso_disp f FF)
  :
  forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ).
Proof.
  intros x' xx'.
  use tpair.
  - set (X:= pr1 H). simpl in X.
    apply (transportb _ (pointwise_inv_is_inv_on f _ ) (X x' xx')).
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
      specialize (XR _ _ _ _ (! iso_after_iso_inv f)).
      etrans. apply XR.
      apply maponpaths_2, homset_property.
    + etrans. apply mor_disp_transportf_prewhisker.
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= inv_mor_after_iso_disp H).
      assert (XRT :=  (maponpaths pr1 XR)).
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'.
      clear XRT' XRT XR.
      assert (XR := @disp_nat_trans_transportf C' C D' D).
      specialize (XR _ _ _ _ (! iso_inv_after_iso f)).
      etrans. apply XR.
      apply maponpaths_2, homset_property.
Defined.

Lemma is_disp_nat_trans_pointwise_inv
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f] yy)
  (H : ∏ (x' : C') (xx' : D' x'),
      is_iso_disp (pointwise_iso_from_nat_iso f x') (pr1 FF x' xx'))
  (x' x0 : C')
  (f0 : x' --> x0)
  (xx' : D' x')
  (xx0 : D' x0)
  (ff : xx' -->[ f0] xx0)
  :
   # (yy : disp_functor _ _ _)  ff ;; (let RT := pr1 (H x0 xx0) in
               transportf (mor_disp (pr1 yy x0 xx0) (pr1 xx x0 xx0))
                 (id_right (pr1 (inv_from_iso f) x0)) RT) =
   transportb (mor_disp (pr1 yy x' xx') (pr1 xx x0 xx0))
     (nat_trans_ax (inv_from_iso f) x' x0 f0)
     ((let RT := pr1 (H x' xx') in
       transportf (mor_disp (pr1 yy x' xx') (pr1 xx x' xx'))
         (id_right (pr1 (inv_from_iso f) x')) RT) ;;
      # (xx : disp_functor _ _ _) ff).
Proof.
 etrans. apply mor_disp_transportf_prewhisker.
    apply pathsinv0.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
(*    Search (?e = ?e' -> ?w = ?w' -> _ ?e ?w = _ ?e' ?w'). *)
    etrans. apply transport_f_f.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
    apply transportf_comp_lemma.
    set (Hx := H x' xx').
    assert (Hx1 := pr2 (pr2 Hx)).
    set (XR:= iso_disp_precomp (pointwise_iso_from_nat_iso f x' ) (_ ,,Hx)).
(*    Check (# (pr1 yy) ff ;; pr1 (H x0 xx0)). *)
    specialize (XR _
       (
        ((# (y : functor _ _ ))%cat f0 · inv_from_iso (pointwise_iso_from_nat_iso f x0))

         )
       ).
    specialize (XR ((xx : disp_functor _ _ _  ) x0 xx0)).
    set (Xweq := make_weq _ XR).
    apply (invmaponpathsweq Xweq).
    unfold Xweq. clear Xweq.
    etrans.  apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2. apply Hx1.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply assoc_disp.
    assert (XRO := @disp_nat_trans_ax _ _ _ _ _ _ _ _ _ FF).
    specialize (XRO _ _ _ xx'  _ ff).
    assert (XR' := ! (transportf_pathsinv0 _ _ _ _  (!XRO))).
    clear XRO.
    clear XR. clear Hx1.
    etrans. apply maponpaths. apply maponpaths_2.
            apply XR'.
    etrans. apply maponpaths.  apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.

    etrans. apply maponpaths.
            apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths.
            apply (inv_mor_after_iso_disp (H _ _ )).
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply maponpaths.
            apply id_right_disp.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    apply maponpaths_2. apply homset_property.
Qed.

Definition inv_disp_from_pointwise_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  :
       yy -->[ inv_from_iso f] xx.
Proof.
  use tpair.
  + intros x' xx'.
    simpl in xx. simpl in yy.
    assert (XR : inv_from_iso (pointwise_iso_from_nat_iso f x') =
                                       pr1 (inv_from_iso f) x').
    { apply id_right. }
    set (RT := pr1 (H x' xx')).
    apply (transportf _ XR RT).
  + intros x' x0 f0 xx' xx0 ff.
    apply is_disp_nat_trans_pointwise_inv.
Defined.

Definition is_disp_functor_cat_iso_if_pointwise_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  : is_iso_disp f FF.
Proof.
  use tpair.
  - apply (inv_disp_from_pointwise_iso _ _ _ _ _ FF H).
  - split.
    + apply subtypePath.
      { intro. apply isaprop_disp_nat_trans_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply disp_nat_trans_transportf.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths. apply (iso_disp_after_inv_mor (H c' xx')).
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
    + apply subtypePath.
      { intro. apply isaprop_disp_nat_trans_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply disp_nat_trans_transportf.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths. apply (inv_mor_after_iso_disp (H c' xx')).
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
Defined.

Definition is_disp_functor_cat_iso_iff_pointwise_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  :
  (∏ x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
    <->
    is_iso_disp f FF.
Proof.
  split.
  - apply is_disp_functor_cat_iso_if_pointwise_iso.
  - apply is_pointwise_iso_if_is_disp_functor_cat_iso.
Defined.

End Functor.
