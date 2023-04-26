Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.
Require Import UniMath.CategoryTheory.DisplayedCats.natural_transformation.
Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.ModelCategories.Retract.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.

Section Face_maps.

Context (C : category).

(* face map 1 now rolls out just as the projection *)
Definition face_map_1 : three C ⟶ arrow C := pr1_category _.

(* we have to define face maps 0 and 2 as proper functors,
since we need the factorization to obtain an object in the arrow
category. *)
Definition face_map_0_data : functor_data (three C) (arrow C).
Proof.
  use make_functor_data.
  - intro xxx.
    use tpair.
    * exact (make_dirprod (three_ob1 xxx) (three_ob2 xxx)).
    * simpl.
      exact (three_mor12 xxx).
  - intros xxx yyy fff.
    simpl.
    (* for morphisms we simply forget the 0th morphism *)
    use tpair.
    * split; simpl.
      + exact (three_mor11 fff).
      + exact (three_mor22 fff).
    * simpl.
      (* commutativity is just commutativity in the lower diagram *)
      symmetry.
      exact (pr2 (three_mor_comm fff)).
Defined.

Definition face_map_0 : three C ⟶ arrow C.
Proof.
  use make_functor.
  - exact face_map_0_data.
  - split.
    * (* unfold functor_idax. *)
      intro.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
    * (* unfold functor_compax. *)
      intros a b c f g.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
Defined.

Definition face_map_2_data : functor_data (three C) (arrow C).
Proof.
  use make_functor_data.
  - intro xxx.
    use tpair.
    * exact (make_dirprod (three_ob0 xxx) (three_ob1 xxx)).
    * simpl.
      exact (three_mor01 xxx).
  - intros xxx yyy fff.
    simpl.
    use tpair.
    * split; simpl.
      + exact (three_mor00 fff).
      + exact (three_mor11 fff).
    * simpl.
      symmetry.
      exact (pr1 (three_mor_comm fff)).
Defined.

Definition face_map_2 : three C ⟶ arrow C.
Proof.
  use make_functor.
  - exact face_map_2_data.
  - split.
    * (* unfold functor_idax. *)
      intro.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
    * (* unfold functor_compax. *)
      intros a b c f g.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
Defined.

(* verify that they are indeed compatible *)
Lemma face_compatibility (fg : three C) : arrow_mor (face_map_0 fg) ∘ arrow_mor (face_map_2 fg) = arrow_mor (face_map_1 fg).
Proof.
  exact (three_comp fg).
Defined.

Definition c_21_data : nat_trans_data face_map_2 face_map_1.
Proof.
  (* this natural transformation boils down to square
    0 ===== 0
    |       |
    |       |
    1 ----> 2
  *)
  intro xxx.
  simpl.
  exists (make_dirprod (identity _) (three_mor12 xxx)).
  simpl.
  rewrite id_left.
  symmetry.
  exact (three_comp xxx).
Defined.

Definition c_21 : face_map_2 ⟹ face_map_1.
Proof.
  use make_nat_trans.
  - exact c_21_data.
  - (* natural transformation commutativity axiom *)
    intros xxx yyy ff.

    (* use displayed properties to turn path in total category
    into path in base category, given our displayed properties

    subtypePath: equality on ∑ x : X, P x is the same as equality
    on X if P is a predicate (maps to a prop).
    In the total category, objects are ∑ c : C, D c
    i.e., objects with displayed data. Morphisms are morphisms
    with displayed data. Our morphisms displayed data is indeed
    propositional: commutative diagram.
    *)
    apply subtypePath.
    * (* For any map in the base category, the induced map
      on the displayed category is a property.

      This is because the induced map is a commuting square,
      so an equality between maps. Therefore, the homset property
      says this is a property. *)
      intro f.
      simpl.
      apply homset_property.
    * (* We are left to prove the commutativity in the base category,
      given our displayed properties. This is effectively just commutativity
      in the bottom square. *)
      cbn.
      rewrite id_left, id_right.
      apply pathsdirprod; trivial.
      symmetry.
      exact (pr2 (three_mor_comm ff)).
Defined.

Definition c_10_data : nat_trans_data face_map_1 face_map_0.
Proof.
  (* this natural transformation boils down to square
    0 ----> 1
    |       |
    |       |
    2 ===== 2
  *)
  intro xxx.
  simpl.
  exists (make_dirprod (three_mor01 xxx) (identity _)).
  simpl.
  rewrite id_right.
  exact (three_comp xxx).
Defined.

Definition c_10 : face_map_1 ⟹ face_map_0.
Proof.
  use make_nat_trans.
  - exact c_10_data.
  - intros xxx yyy ff.
    apply subtypePath.
    * intro x.
      apply homset_property.
    * cbn.
      rewrite id_left, id_right.
      apply pathsdirprod; trivial.
      symmetry.
      exact (pr1 (three_mor_comm ff)).
Defined.

End Face_maps.

Arguments face_map_0 {_}.
Arguments face_map_1 {_}.
Arguments face_map_2 {_}.

(* Lemma face_map_1_preserves_dom {C : category} : ∏ g : three C, arrow_dom (face_map_1 g) = three_ob0 g.
Proof.
  trivial.
Defined.

Lemma face_map_1_preserves_cod {C : category} : ∏ g : three C, arrow_cod (face_map_1 g) = three_ob2 g.
Proof.
  trivial.
Defined. *)

(* Definition face_map_1_section_data (C : category) : functor_data (arrow C) (three C).
Proof.
  use tpair.
  - intros
Defined. *)

(* We can't really do this with the "naive definition" of three C, since then we need
the middle object for the section. We would have to define our own theory.  *)
Definition functorial_factorization (C : category) := section_disp (three_disp C).
Definition fact_section {C : category} (F : functorial_factorization C)
    := section_disp_data_from_section_disp F.
Definition fact_functor {C : category} (F : functorial_factorization C) : arrow C ⟶ three C :=
    section_functor F.
Coercion fact_functor : functorial_factorization >-> functor.

(* Functorial factorizations indeed split face map 1 (d1) *)
Lemma functorial_factorization_splits_face_map_1 {C : category} (F : functorial_factorization C) :
    F ∙ face_map_1 = functor_identity (arrow C).
Proof.
  apply functor_eq; trivial.
  apply homset_property.
Defined.

Definition fact_L {C : category} (F : functorial_factorization C) : arrow C ⟶ arrow C :=
    F ∙ face_map_2.
Definition fact_R {C : category} (F : functorial_factorization C) : arrow C ⟶ arrow C :=
    F ∙ face_map_0.

(* At least now it knows they are compatible *)
Lemma LR_compatibility {C : category} (F : functorial_factorization C) :
    ∏ (f : arrow C), arrow_mor (fact_L F f) · arrow_mor (fact_R F f) = arrow_mor f.
Proof.
  intro.
  exact (three_comp _).
Defined.

Definition Φ {C : category} (F : functorial_factorization C) :
    (fact_L F) ⟹ (functor_identity (arrow C)) :=
  pre_whisker F (c_21 C).

Definition Λ {C : category} (F : functorial_factorization C) :
    (functor_identity (arrow C)) ⟹ (fact_R F) :=
  pre_whisker F (c_10 C).

Definition R_monad_data {C : category} (F : functorial_factorization C)
    (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) : Monad_data (arrow C) :=
  ((fact_R F,, Π),, (Λ F)).

Definition R_monad {C : category} (F : functorial_factorization C)
    (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F))
    (R : Monad_laws (R_monad_data F Π)) : Monad (arrow C) :=
  (R_monad_data F Π,, R).

Definition L_monad_data {C : category} (F : functorial_factorization C)
    (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) : Monad_data (op_cat (arrow C)) :=
  ((functor_opp (fact_L F),, op_nt Σ),, op_nt (Φ F)).

Definition L_monad {C : category} (F : functorial_factorization C)
    (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F))
    (L : Monad_laws (L_monad_data F Σ)) : Monad (op_cat (arrow C)) :=
  (L_monad_data F Σ,, L).

Definition nwfs (C : category) :=
    ∑ (F : functorial_factorization C) (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) ,
    (Monad_laws (L_monad_data F Σ)) × (Monad_laws (R_monad_data F Π)).

Definition make_nwfs {C : category} (F : functorial_factorization C)
    (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) (L : Monad_laws (L_monad_data F Σ))
    (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) (R : Monad_laws (R_monad_data F Π))
        : nwfs C.
Proof.
  exists F, Σ, Π.
  exact (make_dirprod L R).
Defined.

Definition nwfs_fact {C : category} (n : nwfs C) := pr1 n.
Coercion nwfs_fact : nwfs >-> functorial_factorization.
Definition nwfs_Σ {C : category} (n : nwfs C) := pr12 n.
Definition nwfs_Π {C : category} (n : nwfs C) := pr122 n.
Definition nwfs_Σ_laws {C : category} (n : nwfs C) := pr1 (pr222 n).
Definition nwfs_Π_laws {C : category} (n : nwfs C) := pr2 (pr222 n).
Definition nwfs_R_monad {C : category} (n : nwfs C) := R_monad (nwfs_fact n) (nwfs_Π n) (nwfs_Π_laws n).
Definition nwfs_L_monad {C : category} (n : nwfs C) := L_monad (nwfs_fact n) (nwfs_Σ n) (nwfs_Σ_laws n).

(* In a monad algebra, we have [[f αf] laws] : nwfs_R_maps n *)
Definition nwfs_R_maps {C : category} (n : nwfs C) :=
    MonadAlg (nwfs_R_monad n).
Definition nwfs_L_maps {C : category} (n : nwfs C) :=
    MonadAlg (nwfs_L_monad n).

(* the following lemmas about Σ and Π are from
   Grandis, Tholen, (6), (7), diagram after (7), (8), (9) *)

(* diagram after (7) *)
Lemma nwfs_Σ_top_map_id {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor00 (nwfs_Σ n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_L_monad n) f).
  specialize (dirprod_pr1 (pathsdirprodweq (base_paths _ _ law1))) as top.
  apply pathsinv0.
  etrans.
  exact (pathsinv0 top).
  apply id_right.
Qed.

(* σ_f · ρ_{λf} = id (6, 2nd) *)
Lemma nwfs_Σ_bottom_map_inv {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor11 (nwfs_Σ n f) · arrow_mor (fact_R n (fact_L n f)) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_L_monad n) f).
  specialize (dirprod_pr2 (pathsdirprodweq (base_paths _ _ law1))) as bottom.
  exact bottom.
Qed.

(* σ_{λf} · σ_f = F(1_A, σ_f) · σ_f
  where F(1_a, σ_f) is the map on middle objects of F(Σ_f)
  if we see Σ_f as a morphism in the arrow category
   (9, top right + cancel_postcomposition) *)
Lemma nwfs_Σ_bottom_map_L_is_middle_map_of_Σ {C : category} (n : nwfs C) (f : arrow C) :
    (arrow_mor11 (nwfs_Σ n f)) · arrow_mor11 (nwfs_Σ n (fact_L n f)) =
    (arrow_mor11 (nwfs_Σ n f)) · three_mor11 (functor_on_morphisms n (nwfs_Σ n f)).
Proof.
  set (law3 := Monad_law3 (T:=nwfs_L_monad n) f).
  specialize (dirprod_pr2 (pathsdirprodweq (base_paths _ _ law3))) as bottom.
  apply pathsinv0.
  exact bottom.
Qed.

(* diagram after (7) *)
Lemma nwfs_Π_bottom_map_id {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor11 (nwfs_Π n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_R_monad n) f).
  specialize (dirprod_pr2 (pathsdirprodweq (base_paths _ _ law1))) as bottom.
  apply pathsinv0.
  etrans.
  exact (pathsinv0 bottom).
  apply id_left.
Qed.

(* λ_{ρf} · π_f = id (6, 4th) *)
Lemma nwfs_Π_top_map_inv {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor (fact_L n (fact_R n f)) · arrow_mor00 (nwfs_Π n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_R_monad n) f).
  specialize (dirprod_pr1 (pathsdirprodweq (base_paths _ _ law1))) as top.
  exact top.
Qed.

(* π_{ρf} · π_f = F(π_f, 1_b) · π_f)
  where F(π_f, 1_b) = map on middle objects of F(Π_f)
  if we see Π_f as a morphism in the arrow category
   (9, bottom right + cancel_precomposition) *)
Lemma nwfs_Π_bottom_map_R_is_middle_map_of_Π {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor00 (nwfs_Π n (fact_R n f)) · arrow_mor00 (nwfs_Π n f) =
    three_mor11 (functor_on_morphisms n (nwfs_Π n f)) · arrow_mor00 (nwfs_Π n f).
Proof.
  set (law3 := Monad_law3 (T:=nwfs_R_monad n) f).
  specialize (dirprod_pr1 (pathsdirprodweq (base_paths _ _ law3))) as top.
  apply pathsinv0.
  exact top.
Qed.

Definition fact_mor {C : category} (F F' : functorial_factorization C) :=
    section_nat_trans_disp F F'.

Definition fact_mor_nt {C : category} {F F' : functorial_factorization C} (α : fact_mor F F') :=
    section_nat_trans α.
Coercion fact_mor_nt : fact_mor >-> nat_trans.

(* verify that indeed, whiskering with d1 yields id_{C^2} ⟹ id_{C^2} *)
Lemma fact_mor_whisker_d1_is_id {C : category} {F F' : functorial_factorization C}
    (α : fact_mor F F') :
    post_whisker α face_map_1 = nat_trans_id (functor_identity _).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro. (* ~~> identity x = identity x *)
    trivial.
Defined.

(* todo: this goes the other way around, but I think that's the only way? *)
Definition nwfs_L_mor {C : category} {n n' : nwfs C}
    (α : fact_mor n n') : (nwfs_L_monad n') ⟹ (nwfs_L_monad n) :=
  post_whisker (op_nt α) (functor_opp face_map_2).
Definition nwfs_R_mor {C : category} {n n' : nwfs C}
    (α : fact_mor n n') : (nwfs_R_monad n) ⟹ (nwfs_R_monad n') :=
  post_whisker α face_map_0.

Definition nwfs_mor_axioms {C : category} (n n' : nwfs C) (α : fact_mor n n') :=
    Monad_Mor_laws (nwfs_L_mor α) × Monad_Mor_laws (nwfs_R_mor α).

Lemma isaprop_nwfs_mor_axioms {C : category} (n n' : nwfs C) (α : fact_mor n n') :
  isaprop (nwfs_mor_axioms n n' α).
Proof.
  apply isapropdirprod; apply isaprop_Monad_Mor_laws, homset_property.
Qed.

Definition nwfs_mor {C : category} (n n' : nwfs C) :=
    ∑ α : fact_mor n n', nwfs_mor_axioms n n' α.

Lemma isaset_nwfs_mor {C : category} (n n' : nwfs C) : isaset (nwfs_mor n n').
Proof.
  apply isaset_total2.
  - apply isaset_section_nat_trans_disp.
  - intro. apply isasetaprop, isaprop_nwfs_mor_axioms.
Defined.

Definition fact_mor_from_nwfs_mor {C : category} {n n' : nwfs C}
    (α : nwfs_mor n n') := pr1 α.
Coercion fact_mor_from_nwfs_mor : nwfs_mor >-> fact_mor.

Definition nwfs_L_monad_mor {C : category} {n n' : nwfs C}
    (α : nwfs_mor n n') : Monad_Mor (nwfs_L_monad n') (nwfs_L_monad n) :=
  (nwfs_L_mor α,, dirprod_pr1 (pr2 α)).
Definition nwfs_R_monad_mor {C : category} {n n' : nwfs C}
    (α : nwfs_mor n n') : Monad_Mor (nwfs_R_monad n) (nwfs_R_monad n') :=
  (nwfs_R_mor α,, dirprod_pr2 (pr2 α)).

Section NWFS_cat.

Context (C : category).

Definition nwfs_precategory_ob_mor : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (nwfs C).
  - intros n n'.
    exact (nwfs_mor n n').
Defined.

Definition fact_id_is_nwfs_mor (n : nwfs C) : nwfs_mor_axioms n n (section_nat_trans_id (nwfs_fact n)).
Proof.
  (* We just show that fact_id corresponds with the identity monad morphisms
     on L and R. *)
  split.
  - assert (H : nwfs_L_mor (section_nat_trans_id (nwfs_fact n)) = nat_trans_id (nwfs_L_monad n)).
    {
      use nat_trans_eq; [apply homset_property|].
      intro.
      apply subtypePath; [intro; apply homset_property|].
      apply pathsdirprod; cbn; trivial.
    }
    rewrite H.
    exact (Monad_identity_laws _).
  - assert (H : nwfs_R_mor (section_nat_trans_id (nwfs_fact n)) = nat_trans_id (nwfs_R_monad n)).
    {
      use nat_trans_eq; [apply homset_property|].
      intro.
      apply subtypePath; [intro; apply homset_property|].
      apply pathsdirprod; cbn; trivial.
    }
    rewrite H.
    exact (Monad_identity_laws _).
Defined.

Definition nwfs_mor_id (n : nwfs C) : nwfs_mor n n.
Proof.
  use tpair.
  - exact (section_nat_trans_id (nwfs_fact n)).
  - exact (fact_id_is_nwfs_mor n).
Defined.

Definition nwfs_mor_comp (n n' n'' : nwfs C) :
    (nwfs_mor n n') -> (nwfs_mor n' n'') -> (nwfs_mor n n'').
Proof.
  (* Like for identity, we just show that the composition of the morphisms
     corresponds with the composition of the corresponding L and R monad
     morphisms. *)
  intros α α'.

  use tpair.
  - exact (section_nat_trans_comp (fact_mor_from_nwfs_mor α) (fact_mor_from_nwfs_mor α')).
  - split.
    * assert (nwfs_L_mor (section_nat_trans_comp (pr1 α) (pr1 α')) =
              nat_trans_comp _ _ _ (nwfs_L_monad_mor α') (nwfs_L_monad_mor α)) as H.
      {
        simpl.
        use nat_trans_eq.
        - (* for some reason this definition is completely unfolded *)
          exact (homset_property (op_cat (arrow C))).
        - intro x; simpl in x.
          apply subtypePath; [intro; apply homset_property|].
          simpl.
          apply pathsdirprod; cbn.
          * now rewrite id_left.
          * unfold three_mor11.
            simpl.
            unfold mor_disp; simpl.
            (* todo: understand what I have done here *)
            rewrite pr1_transportf.
            (* transport along constant function -> just idfun *)
            rewrite transportf_const.
            trivial.
      }
      unfold fact_mor_from_nwfs_mor.
      rewrite H.
      exact (Monad_composition_laws (nwfs_L_monad_mor α') (nwfs_L_monad_mor α)).
    * assert (nwfs_R_mor (section_nat_trans_comp (pr1 α) (pr1 α')) =
              nat_trans_comp _ _ _ (nwfs_R_monad_mor α) (nwfs_R_monad_mor α')) as H.
      {
        simpl.
        use nat_trans_eq.
        - (* for some reason this definition is completely unfolded *)
          exact (homset_property (arrow C)).
        - intro x; simpl in x.
          apply subtypePath; [intro; apply homset_property|].
          simpl.
          apply pathsdirprod; cbn.
          * unfold three_mor11.
            simpl.
            unfold mor_disp; simpl.
            rewrite pr1_transportf.
            rewrite transportf_const.
            trivial.
          * now rewrite id_left.
      }
      unfold fact_mor_from_nwfs_mor.
      rewrite H.
      exact (Monad_composition_laws (nwfs_R_monad_mor α) (nwfs_R_monad_mor α')).
Defined.

Definition nwfs_precategory_data : precategory_data.
Proof.
  use make_precategory_data.
  - exact nwfs_precategory_ob_mor.
  - exact nwfs_mor_id.
  - exact nwfs_mor_comp.
Defined.

Definition nwfs_is_precategory : is_precategory nwfs_precategory_data.
Proof.
  use make_is_precategory_one_assoc; intros.
  - apply subtypePath; [intro; apply isaprop_nwfs_mor_axioms|cbn].
    apply section_nat_trans_id_left.
  - apply subtypePath; [intro; apply isaprop_nwfs_mor_axioms|cbn].
    apply section_nat_trans_id_right.
  - apply subtypePath; [intro; apply isaprop_nwfs_mor_axioms|cbn].
    apply section_nat_trans_assoc.
Qed.

Definition NWFS_precat : precategory :=
    (nwfs_precategory_data,, nwfs_is_precategory).

Lemma has_homsets_NWFS : has_homsets NWFS_precat.
Proof.
  intros n n' .
  use isaset_nwfs_mor.
Qed.

Definition NWFS : category := (NWFS_precat,, has_homsets_NWFS).

End NWFS_cat.
