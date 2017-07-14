(** **********************************************************

Contents:

- Definition of relative monads [RelMonad]
- Functoriality for relative monads [r_lift]

Reference: % \cite{DBLP:journals/corr/AltenkirchCU14} \par %

Written by: Benedikt Ahrens (started May 2017)


************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of relative monads *)
Section RMonad_def.

Context {C D : precategory} (J : functor C D).

Definition RelMonad_data : UU
  := ∑ F : C -> D, (∏ c, D ⟦J c, F c⟧)
                 × (∏ c d, D ⟦J c, F d⟧ → D ⟦F c, F d⟧).

Definition RelMonad_ob (R : RelMonad_data) (c : C) : D := pr1 R c.
Coercion RelMonad_ob : RelMonad_data >-> Funclass.
Definition r_eta (R : RelMonad_data) c : D ⟦J c, R c⟧ := pr1 (pr2 R) c.
Definition r_bind (R : RelMonad_data) {c d} (f : D⟦J c, R d⟧) : D ⟦R c, R d⟧
  := pr2 (pr2 R) _ _ f.

Definition RelMonad_axioms (R : RelMonad_data) : UU
  := (∏ c, r_bind R (r_eta R c) = identity _ )
   × (∏ c d (f : D⟦J c, R d⟧), r_eta R _ · r_bind R f = f)
   × (∏ c d e (f : D ⟦J c, R d⟧) (g : D ⟦J d, R e⟧),
         r_bind R f · r_bind R g = r_bind R (f · r_bind R g)).

Definition r_bind_r_eta {R : RelMonad_data} (X : RelMonad_axioms R)
  : ∏ c, r_bind R (r_eta R c) = identity _ := pr1 X.
Definition r_eta_r_bind {R : RelMonad_data} (X : RelMonad_axioms R)
  : ∏ c d (f : D⟦J c, R d⟧), r_eta R _ · r_bind R f = f := pr1 (pr2 X).
Definition r_bind_r_bind {R : RelMonad_data} (X : RelMonad_axioms R)
  : ∏ c d e (f : D ⟦J c, R d⟧) (g : D ⟦J d, R e⟧),
         r_bind R f · r_bind R g = r_bind R (f · r_bind R g)
  := pr2 (pr2 X).

Definition RelMonad : UU := ∑ R : RelMonad_data, RelMonad_axioms R.
Coercion RelMonad_data_from_RelMonad (R : RelMonad) : RelMonad_data := pr1 R.
Coercion RelMonad_axioms_from_RelMonad (R : RelMonad) : RelMonad_axioms R := pr2 R.

Definition r_lift (R : RelMonad) {c d : C} (f : c --> d) : R c --> R d
  := r_bind R (#J f · r_eta R _ ).

Definition is_functor_r_lift (R : RelMonad)
  : is_functor (RelMonad_ob R,, @r_lift R).
Proof.
  split; [intro c | intros a b c f g]; cbn; unfold r_lift; cbn.
  - etrans. apply maponpaths.
      etrans. eapply (maponpaths (fun x => x · _  )). apply functor_id.
      apply id_left.
    apply (r_bind_r_eta R).
  - etrans. Focus 2. eapply pathsinv0; apply (r_bind_r_bind R).
    apply maponpaths.
    etrans.
    apply map_on_two_paths. apply functor_comp. apply idpath.
    etrans. Focus 2.
      etrans. Focus 2. apply assoc.
      eapply pathsinv0. apply maponpaths. apply (r_eta_r_bind R).
      apply pathsinv0, assoc.
Defined.

End RMonad_def.