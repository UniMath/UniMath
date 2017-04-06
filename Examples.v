
(** * Examples 

A typical use for displayed categories is for constructing categories of structured objects, over a given (specific or general) category. We give a few examples here:

- category of topological space as total category
- arrow precategories
- objects with N-actions
- elements, over hSet

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.Topology.Topology.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.

Local Open Scope mor_disp_scope.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

(** * Displayed category of topological spaces *)


(** TODO: upstream to Topology.Topology *)
Lemma is_lim_comp {X : UU} {U V : TopologicalSet} (f : X → U) (g : U → V) (F : Filter X) (l : U) :
  is_lim f F l → continuous_at g l →
  is_lim (funcomp f g) F (g l).
Proof.
  apply filterlim_comp.
Qed.
Lemma continuous_comp {X Y Z : TopologicalSet} (f : X → Y) (g : Y → Z) :
  continuous f → continuous g →
  continuous (funcomp f g).
Proof.
  intros Hf Hg x.
  refine (is_lim_comp _ _ _ _ _ _).
  apply Hf.
  apply Hg.
Qed.
Lemma isaprop_continuous ( x y : TopologicalSet)
  (f : x → y)
  : isaprop (continuous (λ x0 : x,  f x0)).
Proof.
  do 3 (apply impred_isaprop; intro).
  apply propproperty.
Qed.
(** END TODO *)

Definition top_disp_precat_ob_mor : disp_precat_ob_mor HSET.
Proof.
  mkpair.
  - intro X. exact (isTopologicalSet (pr1hSet X)).
  - cbn. intros X Y T U f.
    apply (@continuous (pr1hSet X,,T) (pr1hSet Y,,U) f).
Defined.

Definition top_disp_precat_data : disp_precat_data HSET.
Proof.
  exists top_disp_precat_ob_mor.
  mkpair.
  - intros X XX. cbn. unfold continuous. intros. 
    unfold continuous_at. cbn. unfold is_lim. cbn.
    unfold filterlim. cbn. unfold filter_le. cbn.
    intros. assumption.
  - intros X Y Z f g XX YY ZZ Hf Hg. 
    use (@continuous_comp (pr1hSet X,,XX) (pr1hSet Y,,YY) (pr1hSet Z,,ZZ) f g);
      assumption.
Defined.

Definition top_disp_precat_axioms : disp_precat_axioms SET top_disp_precat_data.
Proof.
  repeat split; cbn; intros; try (apply proofirrelevance, isaprop_continuous).
  apply isasetaprop. apply isaprop_continuous.
Defined.
 
Definition top_disp_precat : disp_precat SET := _ ,, top_disp_precat_axioms.


(** ** The displayed arrow category 

A very fertile example: many others can be obtained from it by reindexing. *)
Section Arrow_Disp.

Context (C:Precategory).

Definition arrow_disp_ob_mor : disp_precat_ob_mor (C × C).
Proof.
  exists (fun xy : (C × C) => (pr1 xy) --> (pr2 xy)).
  simpl; intros xx' yy' g h ff'. 
    exact (pr1 ff' ;; h = g ;; pr2 ff')%mor.
Defined.

Definition arrow_id_comp : disp_precat_id_comp _ arrow_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition arrow_data : disp_precat_data _
  := (arrow_disp_ob_mor ,, arrow_id_comp).

Lemma arrow_axioms : disp_precat_axioms (C × C) arrow_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition arrow_disp : disp_precat (C × C)
  := (arrow_data ,, arrow_axioms).

End Arrow_Disp.

(** ** Objects with N-action

For any category C, “C-objects equipped with an N-action” (or more elementarily, with an endomorphism) form a displayed category over C 
Section ZAct. 

Once we have pullbacks of displayed precategories, this can be obtained as a pullback of the previous example. *)

Section NAction.

Context (C:Precategory).

Definition NAction_disp_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun c => c --> c).
  intros x y xx yy f. exact (f ;; yy = xx ;; f)%mor.
Defined.

Definition NAction_id_comp : disp_precat_id_comp C NAction_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    eapply pathscomp0. apply id_left. apply pathsinv0, id_right.
  - simpl; intros x y z f g xx yy zz ff gg.
    eapply pathscomp0. apply @pathsinv0, assoc.
    eapply pathscomp0. apply maponpaths, gg.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition NAction_data : disp_precat_data C
  := (NAction_disp_ob_mor ,, NAction_id_comp).

Lemma NAction_axioms : disp_precat_axioms C NAction_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property. 
Qed.

Definition NAction_disp : disp_precat C
  := (NAction_data ,, NAction_axioms).

End NAction.

(** ** Elements of sets

A presheaf on a (pre)category can be viewed as a fiberwise discrete displayed (pre)category. In fact, the universal example of this is the case corresponding to the identity functor on [SET].  So, having given the displayed category for this case, one obtains it for arbitrary presheaves by reindexing. *)

(* TODO: move? ponder? *)



Section Elements_Disp.

Definition elements_ob_mor : disp_precat_ob_mor SET.
Proof.
  use tpair.
  - simpl. exact (fun X => X).
  - simpl. intros X Y x y f. exact (f x = y).
Defined.

Lemma elements_id_comp : disp_precat_id_comp SET elements_ob_mor.
Proof.
  apply tpair; simpl.
  - intros X x. apply idpath.
  - intros X Y Z f g x y z e_fx_y e_gy_z. cbn.
    eapply pathscomp0. apply maponpaths, e_fx_y. apply e_gy_z.
Qed.

Definition elements_data : disp_precat_data SET
  := (_ ,, elements_id_comp).

Lemma elements_axioms : disp_precat_axioms SET elements_data.
Proof.
  repeat split; intros; try apply setproperty.
  apply isasetaprop; apply setproperty.
Qed.

Definition elements_universal : disp_precat SET
  := (_ ,, elements_axioms).

Definition disp_precat_of_elements {C : Precategory} (P : functor C SET)
  := reindex_disp_precat P elements_universal.

(* TODO: compare to other definitions of this in the library! *)
Definition precat_of_elements {C : Precategory} (P : functor C SET)
  := total_precat (disp_precat_of_elements P).

End Elements_Disp.


Section functor_algebras.

Context {C : Precategory} (F : functor C C).

Definition disp_precat_functor_alg_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (λ c : C, F c --> c).
  intros c d a a' r. exact ( (#F r)%cat · a' = a · r).
Defined.

Definition disp_precat_functor_alg_data : disp_precat_data C.
Proof.
  exists disp_precat_functor_alg_ob_mor.
  split.
  - intros x f. cbn.
    etrans. apply maponpaths_2. apply functor_id.
    etrans. apply id_left. apply pathsinv0, id_right.
  - cbn; intros ? ? ? ? ? ? ? ? H H0.
    etrans. apply maponpaths_2. apply functor_comp.
    etrans. eapply pathsinv0. apply assoc.
    etrans. apply maponpaths. apply H0.
    etrans. apply assoc. 
    etrans. apply maponpaths_2. apply H. 
    apply pathsinv0, assoc.
Defined.

Definition disp_precat_functor_alg_axioms 
  : disp_precat_axioms C disp_precat_functor_alg_data.
Proof.
  repeat split; intros; try apply homset_property.
  apply isasetaprop. apply homset_property.
Qed.

Definition disp_precat_functor_alg : disp_precat C := _ ,, disp_precat_functor_alg_axioms.

Definition total_functor_alg : precategory := total_precat disp_precat_functor_alg.

End functor_algebras.


Section monad_algebras.

Context {C : Precategory} (T : Monad C).

Let T' : C ⟶ C := T.
Let FAlg := total_functor_alg T'.

Definition isMonadAlg (Xa : FAlg) : UU 
  := η T (pr1 Xa) · pr2 Xa = identity _ 
                                      ×
                                      (#T')%cat (pr2 Xa) · pr2 Xa = μ T _ · pr2 Xa.

Definition disp_precat_monad_alg_ob_mor : disp_precat_ob_mor FAlg.
Proof.
  mkpair.
  - exact (λ Xa, isMonadAlg Xa).
  - cbn; intros. exact unit.
Defined.

Definition disp_precat_monad_alg_data : disp_precat_data FAlg.
Proof.
  exists disp_precat_monad_alg_ob_mor.
  split; intros; exact tt.
Defined.

Definition disp_precat_monad_alg_axioms : disp_precat_axioms _ disp_precat_monad_alg_data.
Proof.
  repeat split; cbn; intros; try apply isconnectedunit.
  apply isasetunit.
Defined.
  
End monad_algebras.

(* *)