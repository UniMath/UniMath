Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.
Require Import UniMath.CategoryTheory.ModelCategories.NWFS.
Require Import UniMath.CategoryTheory.ModelCategories.Helpers.

Local Open Scope cat.
Local Open Scope Cat.
Local Open Scope morcls.


Ltac functorial_factorization_mor_eq f := (
  apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|];
  use funextsec;
  intro f;
  use subtypePath; [intro; apply isapropdirprod; apply homset_property|]
).

Section Ff_composition.

Context {C : category}.

(* F' ⊗ F (compose left factors) *)
Definition Ff_lcomp_data (F' F : Ff C) : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro f.
    set (lf := fact_L F f).
    set (rf := fact_R F f).
    set (l'rf := fact_L F' rf).
    set (r'rf := fact_R F' rf).
    exists (arrow_cod l'rf).
    exists (lf · l'rf), r'rf.
    abstract (
      etrans; [apply assoc'|];
      etrans; [apply maponpaths;
               apply (three_comp ((fact_functor F') rf))|];
      simpl;
      etrans; [apply (three_comp (f,, _))|];
      reflexivity
    ).
  - intros f f' γ.
    set (lγ := #(fact_L F) γ).
    set (rγ := #(fact_R F) γ).
    set (l'rγ := #(fact_L F') rγ).
    set (r'rγ := #(fact_R F') rγ).
    exists (arrow_mor00 r'rγ).
    
    abstract (
      split; [
        etrans; [apply assoc'|];
        apply pathsinv0;
        etrans; [apply assoc|];
        etrans; [apply maponpaths_2;
                 exact (arrow_mor_comm lγ)|];
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        exact (arrow_mor_comm l'rγ)
      | apply pathsinv0;
        exact (arrow_mor_comm r'rγ)
      ]
    ).
Defined.

Lemma Ff_lcomp_axioms (F' F : Ff C) : section_disp_axioms (Ff_lcomp_data F' F).
Proof.
  split.
  - intro f.
    set (lf := fact_L F f).
    set (rf := fact_R F f).
    set (l'rf := fact_L F' rf).
    set (r'rf := fact_R F' rf).
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    (* complex rewrite *)
    cbn.
    rewrite (section_disp_id F).
    (* cbn.
    unfold three_mor11.
    cbn. *)
    
    etrans. use (section_disp_on_eq_morphisms' _ (γ := identity rf)).
    etrans. apply maponpaths.
            exact (section_disp_id F' rf).
    reflexivity.
  - intros f f' f'' γ γ'.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    (* simpl.
    unfold arrow_mor00, three_mor11.
    simpl. *)

    apply pathsinv0.
    etrans. apply pr1_section_disp_on_morphisms_comp.
    use section_disp_on_eq_morphisms.
    * apply pr1_section_disp_on_morphisms_comp.
    * reflexivity.
Qed.

Definition Ff_lcomp (F' F : Ff C) : Ff C :=
    (_,, Ff_lcomp_axioms F' F).

Notation "F' ⊗ F" := (Ff_lcomp F' F).

(* I *)
Definition Ff_lcomp_unit_data : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro f.
    exists (arrow_dom f).
    exists (identity _), f.  
    abstract (apply id_left).
  - intros f f' γ.
    exists (arrow_mor00 γ).
    abstract (
      split; [
        etrans; [apply id_left|];
        apply pathsinv0;
        apply id_right
        | apply pathsinv0; exact (arrow_mor_comm γ)]
    ).
Defined.

Definition Ff_lcomp_unit_axioms : section_disp_axioms (Ff_lcomp_unit_data).
Proof.
  split.
  - intro f.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    reflexivity.
  - intros f f' f'' γ γ'.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    reflexivity.
Qed.

Definition Ff_lcomp_unit : Ff C :=
    (_,, Ff_lcomp_unit_axioms).

Definition Ff_l_id_left_data (F : Ff C) : 
    section_nat_trans_disp_data (Ff_lcomp_unit ⊗ F) F.
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; [etrans; [apply id_right|]|]; (
      etrans; [apply id_right|];
      apply pathsinv0;
      apply id_left
    )
  ).
Defined.

Definition Ff_l_id_left_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_left_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  etrans. use pr1_transportf_const.
  etrans. apply id_right.
  apply pathsinv0.
  apply id_left.
Qed.

Definition Ff_l_id_left (F : Ff C) : (Ff_lcomp_unit ⊗ F) --> F :=
    (_,, Ff_l_id_left_axioms F).

Definition Ff_l_id_left_rev_data (F : Ff C) : 
    section_nat_trans_disp_data F (Ff_lcomp_unit ⊗ F).
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; (
      etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [apply id_left|]
    ); [apply id_right|reflexivity]
  ).
Defined.

Definition Ff_l_id_left_rev_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_left_rev_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  etrans. use pr1_transportf_const.
  etrans. apply id_right.
  apply pathsinv0.
  apply id_left.
Qed.

Definition Ff_l_id_left_rev (F : Ff C) : F --> (Ff_lcomp_unit ⊗ F) :=
    (_,, Ff_l_id_left_rev_axioms F).

Definition Ff_l_id_right_data (F : Ff C) : 
    section_nat_trans_disp_data (F ⊗ Ff_lcomp_unit) F.
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; (
      etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [apply id_left|]
    ); [apply pathsinv0; apply id_left|reflexivity]
  ).
Defined.

Definition Ff_l_id_right_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_right_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.

  (* simpl makes it very slow *)
  (* simpl. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.
    
  (* unfold three_mor11.
  cbn. *)
  
  use (section_disp_on_eq_morphisms F (γ := γ)); reflexivity.
Qed.

Definition Ff_l_id_right (F : Ff C) : (F ⊗ Ff_lcomp_unit) --> F :=
    (_,, Ff_l_id_right_axioms F).

Definition Ff_l_id_right_rev_data (F : Ff C) : 
    section_nat_trans_disp_data F (F ⊗ Ff_lcomp_unit).
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; (
      etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [apply id_left|]
    ); [apply id_left|reflexivity]
  ).
Defined.

Definition Ff_l_id_right_rev_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_right_rev_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.
  
  (* simpl makes it very slow *)
  (* simpl. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.

  use section_disp_on_eq_morphisms; reflexivity.
Qed.

Definition Ff_l_id_right_rev (F : Ff C) : F --> (F ⊗ Ff_lcomp_unit) :=
    (_,, Ff_l_id_right_rev_axioms F).

Definition Ff_l_rightwhisker_data 
      {G G' : Ff C} (τ : section_nat_trans_disp G G')
      (F : Ff C) :
    section_nat_trans_disp_data (G ⊗ F) (G' ⊗ F).
Proof.
  intro f.
  (* cbn. *)
  set (τρf := τ (fact_R F f)).
  destruct τρf as [mor [comm1 comm2]].
  exists (mor).
  abstract (
    split; [
      etrans; [apply assoc'|];
      apply pathsinv0;
      etrans; [apply id_left|];
      apply cancel_precomposition;
      apply pathsinv0;
      etrans; [exact comm1|];
      apply id_left
    | etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [exact (pathsinv0 comm2)|];
      apply id_right
    ]
  ).
Defined.

Definition Ff_l_rightwhisker_axioms 
      {G G'} (τ : section_nat_trans_disp G G') 
      (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_rightwhisker_data τ F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.

  destruct τ as [τ τax].
  set (τcommf := base_paths _ _ (τax _ _ (#(fact_R F) γ))).
  apply pathsinv0.
  etrans. exact (pathsinv0 τcommf).
  etrans. use pr1_transportf_const.
  reflexivity.
Qed.

Definition Ff_l_rightwhisker {G G'} (τ : G --> G') (F : Ff C) :
    (G ⊗ F) --> (G' ⊗ F) :=
  (_,, Ff_l_rightwhisker_axioms τ F).

Notation "τ ⊗post F" := (Ff_l_rightwhisker τ F) (at level 50).


Lemma Ff_l_rightwhisker_id (G F : Ff C) :
    ((identity G) ⊗post F) = identity _.
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  reflexivity.
Qed.

Lemma Ff_l_rightwhisker_comp {G G' G'' : Ff C}
    (τ : G --> G') (τ' : G' --> G'') (F : Ff C)  :
  ((τ · τ') ⊗post F) = (τ ⊗post F) · (τ' ⊗post F).
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  (* cbn makes it very slow *)
  (* cbn. *)

  etrans. use (pr1_transportf_const).
  apply pathsinv0.
  etrans. use (pr1_transportf_const).
  reflexivity.
Qed.

Definition Ff_l_leftwhisker_data (F : Ff C) {G G'} (τ : section_nat_trans_disp G G') :
    section_nat_trans_disp_data (F ⊗ G) (F ⊗ G').
Proof.
  intro f.
  
  (* destruct (τ f) as [τf [commτ1 commτ2]]. *)
  set (ρGf := fact_R G f).
  set (ρG'f := fact_R G' f).
  set (γρ := three_mor_mor12 (section_nat_trans τ f) : ρGf --> ρG'f).
  
  set (Fγρ := (section_disp_on_morphisms (section_disp_data_from_section_disp F) γρ)).
  exists (pr1 Fγρ).
  set (comm := pr2 Fγρ).
  simpl in comm.

  (* commutativity of diagram
       =======
     |         |
  λG |         | λG'
     v   τf    v
       ------>   
     |         |
λFρG |         | λFρG'
     v   τρf   v
     □ ------>□  
     |         |
ρFρG |         | ρFρG'
     v         v  
       =======   
    *)
  abstract (
    split; [
      etrans; [apply assoc'|];
      etrans; [apply maponpaths; exact (pr1 comm)|];
      etrans; [apply assoc|];
      apply pathsinv0; 
      etrans; [apply assoc|];
      apply cancel_postcomposition;
      exact (pathsinv0 (pr12 (τ f)))|
      exact (pr2 comm)
    ]
  ).
Defined.

Definition Ff_l_leftwhisker_axioms (F : Ff C) {G G'} (τ : section_nat_trans_disp G G') :
    section_nat_trans_disp_axioms (Ff_l_leftwhisker_data F τ).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.
  (* simpl.
  unfold three_mor11.
  cbn. *)

  etrans. use (pr1_section_disp_on_morphisms_comp F).
  apply pathsinv0.
  etrans. use (pr1_section_disp_on_morphisms_comp F).

  (* destruct τ as [τ τax]. *)
  (* unfold section_nat_trans_disp_axioms in τax. *)
  set (τcommf := base_paths _ _ 
                  ((section_nt_disp_axioms_from_section_nt_disp τ) _ _ γ)).

  use (section_disp_on_eq_morphisms F).
  - (* cbn makes it very slow *)
    (* cbn. *)
    etrans. exact (pathsinv0 τcommf).
    etrans. use pr1_transportf_const.
    reflexivity.
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_right.
    reflexivity.
Qed.

Definition Ff_l_leftwhisker (F : Ff C) {G G'} (τ : G --> G') :
    (F ⊗ G) --> (F ⊗ G') :=
  (_,, Ff_l_leftwhisker_axioms F τ).

Notation "F ⊗pre τ" := (Ff_l_leftwhisker F τ) (at level 50).

Lemma Ff_l_leftwhisker_id (F G : Ff C) :
    (F ⊗pre (identity G)) = identity _.
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  (* cbn makes it very slow *)
  (* cbn. *)
  etrans. use (section_disp_on_eq_morphisms' F (γ := identity _)).
  etrans. apply maponpaths.
          use (section_disp_id F _).
  reflexivity.
Qed.

Lemma Ff_l_leftwhisker_comp (F : Ff C) {G G' G'' : Ff C}
    (τ : G --> G') (τ' : G' --> G'') :
  (F ⊗pre (τ · τ')) = (F ⊗pre τ) · (F ⊗pre τ').
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  apply pathsinv0.
  etrans. use (pr1_transportf_const).
  
  (* cbn. *)
  etrans. use (pr1_section_disp_on_morphisms_comp F).
  
  use (section_disp_on_eq_morphisms F).
  - apply pathsinv0.
    etrans. use (pr1_transportf_const).
    reflexivity.
  - apply id_left.
Qed.

Definition Ff_l_assoc_rev_data (F F' F'' : Ff C) :
    section_nat_trans_disp_data (F ⊗ (F' ⊗ F'')) ((F ⊗ F') ⊗ F'') .
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; 
      (etrans; [apply id_right|];
       apply pathsinv0;
       etrans; [apply id_left|]); 
          [apply assoc|reflexivity]
  ).
Defined.

Definition Ff_l_assoc_rev_axioms (F F' F'' : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_assoc_rev_data F F' F'').
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.
  (* cbn makes it very slow *)
  (* cbn. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.
  
  (* unfold three_mor11.
  simpl. *)

  use (section_disp_on_eq_morphisms F); reflexivity.
Qed.

Definition Ff_l_assoc_rev (F F' F'' : Ff C) :
    (F ⊗ (F' ⊗ F'')) --> ((F ⊗ F') ⊗ F'') :=
  (_,, Ff_l_assoc_rev_axioms F F' F'').


Definition Ff_l_assoc_data (F F' F'' : Ff C) :
    section_nat_trans_disp_data ((F ⊗ F') ⊗ F'') (F ⊗ (F' ⊗ F'')).
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; 
      (etrans; [apply id_right|];
       apply pathsinv0;
       etrans; [apply id_left|]); 
          [apply assoc'|reflexivity]
  ).
Defined.

Definition Ff_l_assoc_axioms (F F' F'' : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_assoc_data F F' F'').
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.
  (* cbn makes it very slow *)
  (* cbn. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.
  
  (* unfold three_mor11.
  simpl. *)
  use (section_disp_on_eq_morphisms F); reflexivity.
Qed.

Definition Ff_l_assoc (F F' F'' : Ff C) :
    ((F ⊗ F') ⊗ F'') --> (F ⊗ (F' ⊗ F'')) :=
  (_,, Ff_l_assoc_axioms F F' F'').

Definition Ff_l_mor_comp {F F' G G' : Ff C} 
    (τ : F --> F') (ρ : G --> G') :
  (F ⊗ G) --> (F' ⊗ G').
Proof.
  exact ((τ ⊗post G) · (F' ⊗pre ρ)).
Defined.

Definition Ff_l_point_data (F : Ff C) :
    section_nat_trans_disp_data Ff_lcomp_unit F.
Proof.
  intro f.
  exists (fact_L F f).
  abstract (
    split; [
      reflexivity|
      rewrite id_right;
      apply pathsinv0;
      exact (three_comp (fact_functor F f))
    ]
  ).
Defined.

Definition Ff_l_point_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_point_data F).
Proof.
  intros f g γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  etrans. apply pr1_transportf_const.
  exact (arrow_mor_comm (#(fact_L F) γ)).
Qed.

Definition Ff_l_point (F : Ff C) :
    Ff_lcomp_unit --> F :=
  (_,, Ff_l_point_axioms F).

End Ff_composition.


(* redefine notation *)
Notation "F ⊗ F'" := (Ff_lcomp F F').
Notation "F ⊗pre τ" := (Ff_l_leftwhisker F τ) (at level 50).
Notation "τ ⊗post F" := (Ff_l_rightwhisker τ F) (at level 50).
Notation "τ ⊗prod ρ" := (Ff_l_mor_comp τ ρ) (at level 50).


Require Import CategoryTheory.Monoidal.Categories.

Section Ff_monoidal.

Context {C : category}.

Definition Ff_tensor_data : tensor_data (Ff C).
Proof.
  use tpair.
  - exact (Ff_lcomp).
  - split.
    * exact (Ff_l_leftwhisker).
    * exact (λ b _ _ γ, Ff_l_rightwhisker γ b).
Defined.

Definition Ff_monoidal_data : monoidal_data (Ff C).
Proof.
  use make_monoidal_data.
  - exact Ff_tensor_data.
  - exact Ff_lcomp_unit.
  - exact Ff_l_id_left.
  - exact Ff_l_id_left_rev.
  - exact Ff_l_id_right.
  - exact Ff_l_id_right_rev.
  - exact Ff_l_assoc.
  - exact Ff_l_assoc_rev.
Defined.

Definition Ff_monoidal_laws : monoidal_laws Ff_monoidal_data.
Proof.
  repeat split.
  - intros F F'.
    functorial_factorization_mor_eq f.
    cbn.
    etrans. use (section_disp_on_eq_morphisms F (γ' := identity _)); reflexivity. 
    etrans. apply maponpaths. apply (section_disp_id F).
    reflexivity.
  - intros F F'.
    functorial_factorization_mor_eq f.
    reflexivity.
  - intros A F F' F'' γ γ'.
    functorial_factorization_mor_eq f.
    (* cbn. *)
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    (* cbn. *)
    etrans. use (pr1_section_disp_on_morphisms_comp A).
    use (section_disp_on_eq_morphisms A).
    * apply pathsinv0.
      etrans. use pr1_transportf_const.
      reflexivity.
    * apply id_left.
  - intros A F F' F'' γ γ'.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    reflexivity.
  - intros A F F' F'' γ γ'.
    apply pathsinv0.
    functorial_factorization_mor_eq f.
    (* cbn. *)
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    (* cbn. *)
    set (mor := three_mor_mor12 (section_nat_trans γ' f) : fact_R F' f --> fact_R F'' f).

    set (γnaturality := section_nt_disp_axioms_from_section_nt_disp γ).
    set (γnatf := γnaturality _ _ mor).
    set (γnatfb := base_paths _ _ γnatf).
    etrans. exact (pathsinv0 γnatfb).
    etrans. use pr1_transportf_const.
    apply cancel_postcomposition.
    use (section_disp_on_eq_morphisms A); reflexivity.
  - intros F F' γ.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    (* cbn. *)
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_right.
    reflexivity.
  - functorial_factorization_mor_eq f.
    (* cbn. *)
    etrans. use pr1_transportf_const.
    apply id_left.
  - functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply id_left.
  - intros F F' γ.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    apply pathsinv0.
    apply id_right.
  - functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply id_left.
  - functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply id_left.
  - intros A F F' F'' γ.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    use (section_disp_on_eq_morphisms A); reflexivity.
  - intros A F F' F'' γ.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
  - intros A F F' F'' γ.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    use (section_disp_on_eq_morphisms A); reflexivity.
  - functorial_factorization_mor_eq f. 
    etrans. use pr1_transportf_const.
    apply id_left.
  - functorial_factorization_mor_eq f. 
    etrans. use pr1_transportf_const.
    apply id_left.
  - intros F F'.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    etrans. use (section_disp_on_eq_morphisms F (γ' := identity _)); reflexivity.
    etrans. apply maponpaths.
            apply (section_disp_id F).
    reflexivity.
  - intros A F F' F''.
    functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    etrans. apply cancel_postcomposition.
            use pr1_transportf_const.
    
    etrans. apply cancel_precomposition.
    {
      etrans. apply (section_disp_on_eq_morphisms A (γ' := identity _)); reflexivity.
      apply maponpaths.
      apply (section_disp_id A).
    }
    etrans. apply id_right.
    etrans. apply id_right.

    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    reflexivity.
Qed.

Definition Ff_monoidal : monoidal (Ff C) :=
    (_,, Ff_monoidal_laws).

End Ff_monoidal.

Require Import CategoryTheory.Monads.Monads.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.

Section Ff_monoid_is_RNWFS.

Context {C : category}.


Definition Ff_monoid_is_RNWFS_mul_data 
    {F : Ff C} (R : monoid (Ff_monoidal) F) :
  nat_trans_data (functor_composite (fact_R F) (fact_R F)) (fact_R F).
Proof.
  intro f.

  set (μ := monoid_data_multiplication _ R).
  set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
  exact (three_mor_mor12 (section_nat_trans μ f)).
Defined.

Lemma Ff_monoid_is_RNWFS_mul_axioms 
    {F : Ff C} (R : monoid (Ff_monoidal) F) :
  is_nat_trans _ _ (Ff_monoid_is_RNWFS_mul_data R).
Proof.
  intros f f' γ.

  set (μ := monoid_data_multiplication _ R).
  set (μaxγ := (section_nt_disp_axioms_from_section_nt_disp μ) _ _ γ).
  set (μaxγb := base_paths _ _ μaxγ).
  
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - (* cbn.
    cbn in μaxγb. *)
    apply pathsinv0.
    etrans. exact (pathsinv0 μaxγb).
    etrans. use pr1_transportf_const.
    apply cancel_postcomposition.
    use (section_disp_on_eq_morphisms F); reflexivity.
  - etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    reflexivity.
Qed.

Definition Ff_monoid_is_RNWFS_mul 
      {F : Ff C} (R : monoid (Ff_monoidal) F) :
    (functor_composite (fact_R F) (fact_R F)) ⟹ (fact_R F) :=
  (_,, Ff_monoid_is_RNWFS_mul_axioms R).

Lemma Ff_point_unique 
    {F : Ff C} 
    (γ : Ff_lcomp_unit --> F) :
  γ = Ff_l_point F.
Proof.
  apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
  use funextsec.
  intro f.
  use subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  set (test := three_mor_comm (section_nat_trans γ f)).
  use (pathscomp1 (pr1 (three_mor_comm (section_nat_trans γ f)))).
  - apply id_left.
  - apply id_left.
Qed.

Lemma Ff_monoid_is_RNWFS_monad_laws 
    {F : Ff C} (R : monoid (Ff_monoidal) F) :
  disp_Monad_laws (R_monad_data F (Ff_monoid_is_RNWFS_mul R)).
Proof.
  set (μ := monoid_data_multiplication _ R).
  
  repeat split.
  - intro f.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [|apply id_left].
    
    set (μax := monoid_to_unit_left_law _ R).
    set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
    set (μaxf := eq_section_nat_trans_disp_on_morphism μax f).
    set (μaxfb := base_paths _ _ μaxf).
    
    apply pathsinv0.
    etrans. exact (pathsinv0 μaxfb).
    etrans. use pr1_transportf_const.
    
    apply cancel_postcomposition.
    (* rewrites in term *)
    rewrite (Ff_point_unique _).
    reflexivity.
  - intro f.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [|apply id_left].

    set (μax := monoid_to_unit_right_law _ R).
    set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
    set (μaxf := eq_section_nat_trans_disp_on_morphism μax f).
    set (μaxfb := base_paths _ _ μaxf).

    apply pathsinv0.
    etrans. exact (pathsinv0 μaxfb).
    etrans. use pr1_transportf_const.

    apply cancel_postcomposition.
    (* rewrites in term *)
    rewrite (Ff_point_unique (monoid_data_unit Ff_monoidal R)).
    apply pathsinv0.
    etrans. apply (section_disp_on_eq_morphisms F (γ' := three_mor_mor12 (section_nat_trans (Ff_l_point F) f))); reflexivity.
    reflexivity.
  - intro f.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [|reflexivity].

    set (μax := monoid_to_assoc_law _ R).
    set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
    set (μaxf := eq_section_nat_trans_disp_on_morphism μax f).
    set (μaxfb := base_paths _ _ μaxf).

    use (pathscomp1 μaxfb).
    * etrans. use pr1_transportf_const.
      (* cbn.
      unfold three_mor11.
      cbn. *)
      apply cancel_postcomposition.
      etrans. use pr1_transportf_const.
      etrans. apply id_left.
      reflexivity.
    * etrans. use pr1_transportf_const.
      apply cancel_postcomposition.
      reflexivity.
Qed.

Definition Ff_monoid_is_RNWFS 
      {F : Ff C} (R : monoid (Ff_monoidal) F) :
    rnwfs_over F.
Proof.
  exists (Ff_monoid_is_RNWFS_mul R).
  exact (Ff_monoid_is_RNWFS_monad_laws R).
Defined.

End Ff_monoid_is_RNWFS.