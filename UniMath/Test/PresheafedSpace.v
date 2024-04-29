Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.Test.Opens.
Require Import UniMath.Test.Presheaves.

Local Open Scope subtype.
Local Open Scope cat.

Section Sheaves.

  Context (C : category).
  Context (HC : is_univalent C).

  Definition presheafed_space
    : UU
    := ∑ (T : TopologicalSpace), presheaf_cat C T.

  Definition presheafed_space_hom
    (X X' : presheafed_space)
    : UU
    := ∑ (f: continuous_function (pr1 X) (pr1 X')), presheaf_cat C (pr1 X') ⟦pr2 X', pushforward f (pr2 X)⟧.

  Lemma presheafed_space_hom_eq
    (X X' : presheafed_space)
    (F F' : presheafed_space_hom X X')
    (H1 : pr1 F = pr1 F')
    (H2 : nat_trans_comp _ _ _ (pr2 F) (idtomor (C := [_, _]) _ _ (maponpaths (λ x, pushforward x (pr2 X)) H1)) = pr2 F')
    : F = F'.
  Proof.
    induction F as [base c].
    induction F' as [base' c'].
    cbn in H1.
    induction H1.
    cbn in H2.
    now induction (!nat_trans_comp_id_right (homset_property _) _ _ c @ H2).
  Qed.

  Definition presheafed_space_id
    (X : presheafed_space)
    : presheafed_space_hom X X.
  Proof.
    exists (identity (pr1 X : top_cat)).
    apply inv_from_z_iso.
    apply pushforward_id.
  Defined.

  Definition presheafed_space_comp
    {X X' X'' : presheafed_space}
    (F : presheafed_space_hom X X')
    (F' : presheafed_space_hom X' X'')
    : presheafed_space_hom X X''.
  Proof.
    exists ((pr1 F : top_cat⟦_, _⟧) · pr1 F').
    refine (nat_trans_comp _ _ _ (pr2 F') _).
    refine (nat_trans_comp _ _ _ (pre_whisker _ (pr2 F)) _).
    exact (inv_from_z_iso (pushforward_comp (pr1 F) (pr1 F') _)).
  Defined.

  Local Notation "α >> β" := (nat_trans_comp _ _ _ α β) (at level 50, left associativity).

  Definition presheafed_space_id_right
    (X X' : presheafed_space)
    (F : presheafed_space_hom X X')
    : presheafed_space_comp F (presheafed_space_id X') = F.
  Proof.
    use presheafed_space_hom_eq.
    - apply (id_right (C := top_cat)).
    - apply nat_trans_eq_alt.
      intro U.
      refine (maponpaths (λ x, _ · (_ · x) · _) (id_left _) @ _).
      refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
      refine (maponpaths (λ x, _ · x · _) (functor_comp (pr2 X) _ _) @ _).
      refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
      refine (maponpaths (λ x, _ · x · _ · _) (functor_id (pr2 X) _) @ _).
      refine (maponpaths (λ x, x · _ · _) (id_right _) @ _).
      refine (maponpaths (λ x, _ x · _ · _ · _) (idpath _ : _ = identity (C := (topological_space_category (pr1 X'))^op) U) @ _).
      refine (maponpaths (λ x, x · _ · _ · _) (functor_id (C := (topological_space_category (pr1 X'))^op) (C' := C) (pr2 X') U) @ _).
      rewrite (functor_id (pr2 X')).
      + exact .
        match goal with
        | [ |- # ?a ?b = _ ] => pose a; pose b
        end.
        rewrite (functor_id (pr2 X')).
        refine (functor_id (C := (topological_space_category (pr1 X'))^op) (pr2 X') (U) @ _).
        Set Printing Implicit.
        exact p.
        simpl.
      }
      simpl.
      refine (maponpaths (λ x, _ · x · _) _ @ _).
      {
        simpl.
      }
      refine (maponpaths (λ x, _ · (# (pr2 X : _ ⟶ _) x) · _) (idpath _ : a = identity (C := x) (continuous_open_preimage ((pr1 F : top_cat⟦_, _⟧) · identity (pr1 X' : top_cat)) U : x)) @ _).
      rewrite (functor_id (pr2 X) _).
      +
      rewrite (functor_id (pr2 X)).
      pose .
      rewrite p.
      rewrite functor_id.


      refine (maponpaths (λ x, _ · x · _) _ @ _).
      +         refine (functor_id (pr2 X) _).
        apply functor_id.
        exact (functor_id (C := y) (pr2 X) a).
        unfold topological_space_category, opp_precat in c.
        epose (functor_data_from_functor p _ (pr2 X : _ ⟶ _)).
        cbn in p, c.
        unfold opp_precat_data in c.
        cbn in c.
        unfold opp_precat_ob_mor in c.
        cbn in c.
        unfold make_precategory_data in p.
        unfold make_precategory_ob_mor in p.
        cbn in p.
        unfold make_dirprod in p.
        cbn in p.

        match b with
        | p ⟶ _ => idtac
        end.
        match goal with
        | [ |- # (?b' : p ⟶ _) _ = _ ] => pose b'
        end.
        Set Printing Implicit.

        epose (H := functor_id (pr2 X) a).
        exact H.
  Qed.

  (* Definition space_with_local_data_disp_cat
    : disp_cat (total_category disp_top).
  Proof.
    use tpair.
    - use tpair.
      + exists D_presheaf.
        intros T T' P P' F.
        exact ((P' : _ ⟶ _) ⟹ (D_presheaf_pushforward F P : _ ⟶ _)).
      + split.
        * intros T P.
          exact (z_iso_mor (idtoiso (C := [_, _]) (!D_presheaf_pushforward_id T P))).
        * intros X Y Z F F' P P' P'' H H'.
          apply (nat_trans_comp _ _ _ H').
          apply (nat_trans_comp _ _ _ (pre_whisker _ H)).
          refine (post_whisker (G := functor_opp (continuous_to_functor F') ∙ functor_opp (continuous_to_functor F)) (nat_trans_id (functor_opp (continuous_to_functor (F · F')))) P).
    - repeat split.
      + intros T T' F P P' H.
        apply nat_trans_eq_alt.
        intro t.
        unfold transportb.
        unfold nat_trans_data_from_nat_trans_funclass.
        unfold mor_disp.
        simpl.
        rewrite (functtransportf (λ f, )).
        rewrite functtransportf
        rewrite pr1_transportf.
        cbn in *.
        Search (pr1 (transportf _ _ _)).
        refine (_ @ !maponpaths (λ x, x t) (pr1_transportf (A := (pr1 T : hSet) → (pr1 T' : hSet)) (B := continuous) (P := λ f H, (P' : _ ⟶ _) ⟹ functor_composite_data (functor_opp_data (continuous_to_functor (f ,, H))) (P : _ ⟶ _)) (!id_left _) H)).
        unfold mor_disp.
        cbn in *.
        epose (transportf_fun).
        epose (functtransportf).
        unfold transportb.

        Search (transportb ()).
  Defined. *)

End Sheaves.
