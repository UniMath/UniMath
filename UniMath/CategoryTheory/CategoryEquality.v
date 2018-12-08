(* ----------------------------------------------------------------------------------- *)
(** ** Equality of precategories

   Goal: two precategories are equal iff we have an isomorphism between them.
   We use a chain of equivalences. Each step refines the data a bit.                   *)
(* ----------------------------------------------------------------------------------- *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.catiso.

Open Scope cat.

(* MOVE SOMEWHERE ELSE? *)
Definition path_sigma_hprop
           {A : UU}
           (B : A → UU)
           (x y : ∑ (z : A), B z)
           (HB : isaprop (B (pr1 y)))
  : x = y ≃ pr1 x = pr1 y.
Proof.
  refine (weqpr1 _ _ ∘ total2_paths_equiv _ _ _)%weq.
  intros.
  apply HB.
Defined.

(** Step 1 *)
Definition path_precat
           (C D : precategory)
           (HD : has_homsets D)
  : C = D ≃ precategory_data_from_precategory C = D.
Proof.
  refine (path_sigma_hprop _ _ _ _).
  apply isaprop_is_precategory.
  apply HD.
Defined.

(** Step 2 *)
Definition data_cat_eq_1
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : UU
  := transportf (λ z, z → z → UU) Fo (@precategory_morphisms C)
     =
     @precategory_morphisms D.

Definition cat_eq_1
           (C D : precategory_data)
  : UU
  := ∑ (F : ∑ (Fo : ob C = ob D), data_cat_eq_1 C D Fo),
       (pr1 (transportf (λ x, precategory_id_comp x)
                        (total2_paths_f (pr1 F) (pr2 F))
                        (pr2 C))
        = pr1 (pr2 D))
     ×
       pr2 (transportf (λ x, precategory_id_comp x)
                       (total2_paths_f (pr1 F) (pr2 F))
                       (pr2 C))
       =
       pr2(pr2 D).

Definition cat_path_to_cat_eq_1
           (C D : precategory_data)
  : C = D ≃ cat_eq_1 C D.
Proof.
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  use weqbandf.
  - apply total2_paths_equiv.
  - intro p ; cbn.
    induction C as [C HC].
    induction D as [D HD].
    cbn in *.
    induction p ; cbn ; unfold idfun.
    refine (_ ∘ total2_paths_equiv _ _ _)%weq.
    use weqfibtototal.
    intros p.
    cbn.
    rewrite transportf_const.
    exact (idweq _).
Defined.

(** Step 3 *)
Definition data_cat_eq_2
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : UU
  := ∏ (a b : ob C), C⟦a,b⟧ = D⟦eqweqmap Fo a,eqweqmap Fo b⟧.

Definition cat_eq_2
           (C D : precategory_data)
  : UU
  := ∑ (F : ∑ (Fo : ob C = ob D), data_cat_eq_2 C D Fo),
       (∏ (a : C), eqweqmap (pr2 F a a) (identity a) = identity (eqweqmap (pr1 F) a))
     ×
       (∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧),
         eqweqmap (pr2 F a c) (f · g)
         =
         eqweqmap (pr2 F a b) f · eqweqmap (pr2 F b c) g).

Definition data_cat_eq_1_to_2
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : data_cat_eq_1 C D Fo ≃ data_cat_eq_2 C D Fo.
Proof.
  induction C as [C HC].
  induction C as [CO CM].
  induction D as [D HD].
  induction D as [DO DM].
  cbn in *.
  induction Fo.
  unfold data_cat_eq_1, data_cat_eq_2.
  cbn.
  refine (_ ∘ weqtoforallpaths _ _ _)%weq.
  use weqonsecfibers.
  intros x.
  exact (weqtoforallpaths _ _ _)%weq.
Defined.

Definition cat_eq_1_to_cat_eq_2
           (C D : precategory_data)
           (DS : ∏ (x y : D), isaset (precategory_morphisms x y))
  : cat_eq_1 C D ≃ cat_eq_2 C D.
Proof.
  use weqbandf.
  - use weqfibtototal.
    intro p.
    exact (data_cat_eq_1_to_2 C D p).
  - intros p.
    induction C as [C HC].
    induction C as [CO CM].
    induction HC as [CI CC].
    induction D as [D HD].
    induction D as [DO DM].
    induction HD as [DI DC].
    induction p as [p1 p2] ; cbn in *.
    unfold data_cat_eq_1 in p2.
    induction p1 ; cbn in *.
    induction p2 ; cbn ; unfold idfun.
    use weqdirprodf.
    + use weqimplimpl.
      * intros f a.
        induction f.
        reflexivity.
      * intros f.
        apply funextsec.
        intro z.
        apply f.
      * intro.
        apply impred_isaset.
        intro.
        apply DS.
      * apply impred.
        intro.
        apply DS.
    + use weqimplimpl.
      * intros p.
        induction p.
        reflexivity.
      * intros p.
        apply funextsec ; intro a.
        apply funextsec ; intro b.
        apply funextsec ; intro c.
        apply funextsec ; intro f.
        apply funextsec ; intro g.
        specialize (p a b c f g).
        induction p.
        reflexivity.
      * repeat (apply impred_isaset ; intro).
        apply DS.
      * repeat (apply impred ; intro).
        apply DS.
Defined.

(** Step 4 *)
Definition cat_equiv
           (C D : precategory_data)
  : UU
  := ∑ (F : ∑ (Fo : ob C ≃ D), ∏ (a b : ob C), C⟦a,b⟧ ≃ D⟦Fo a,Fo b⟧),
       (∏ (a : C), (pr2 F) a a (identity a) = identity (pr1 F a))
     ×
       (∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧), pr2 F a c (f · g) = pr2 F a b f · pr2 F b c g).

Definition weq_cat_eq_cat_equiv
           (C D : precategory_data)
  : cat_eq_2 C D ≃ cat_equiv C D.
Proof.
  use weqbandf.
  - use weqbandf.
    + apply univalence.
    + intros p.
      unfold data_cat_eq_2.
      use weqonsecfibers.
      intros x.
      use weqonsecfibers.
      intros y.
      apply univalence.
  - intros q.
    apply idweq.
Defined.

(** Step 5 *)
Definition cat_equiv_to_catiso
           (C D : precategory_data)
  : cat_equiv C D → catiso C D.
Proof.
  intros F.
  use tpair.
  - use tpair.
    + use tpair.
      * exact (pr1(pr1 F)).
      * exact (pr2(pr1 F)).
    + split.
      * exact (pr1(pr2 F)).
      * exact (pr2(pr2 F)).
  - split.
    + intros a b.
      apply (pr2(pr1 F)).
    + apply (pr1(pr1 F)).
Defined.

Definition catiso_to_cat_equiv
           (C D : precategory_data)
  : catiso C D → cat_equiv C D.
Proof.
  intros F.
  use tpair.
  - use tpair.
    + use weqpair.
      * exact (functor_on_objects F).
      * apply F.
    + intros a b.
      use weqpair.
      * exact (functor_on_morphisms F).
      * apply F.
  - split.
    + exact (functor_id F).
    + exact (@functor_comp _ _ F).
Defined.

Definition cat_equiv_to_catiso_weq
           (C D : precategory)
  : cat_equiv C D ≃ catiso C D.
Proof.
  refine (cat_equiv_to_catiso C D ,, _).
  use isweq_iso.
  - exact (catiso_to_cat_equiv C D).
  - reflexivity.
  - reflexivity.
Defined.

(** All in all, we get *)
Definition catiso_is_path_precat
           (C D : precategory)
           (HD : has_homsets D)
  : C = D ≃ catiso C D
  := ((cat_equiv_to_catiso_weq C D)
        ∘ weq_cat_eq_cat_equiv C D
        ∘ cat_eq_1_to_cat_eq_2 C D HD
        ∘ cat_path_to_cat_eq_1 C D
        ∘ path_precat C D HD)%weq.