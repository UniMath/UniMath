Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.cats.limits.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.polynomialfunctors.
Require Import UniMath.CategoryTheory.exponentials.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Ltac etrans := eapply pathscomp0.

Section rightkanextension.

Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.CommaCategories.

Variables M C A : precategory.
Variables (K : functor M C).
Variables (hsC : has_homsets C) (hsA : has_homsets A).
Variables (LA : Lims A).

Local Notation "c ↓ K" := (cComma hsC K c) (at level 30).

Section fix_T.

Variable (T : functor M A).

Local Definition Q (c : C) : functor (c ↓ K) M := cComma_pr1 hsC K c.

Local Definition QT (c : C) := functor_composite (Q c) T.

Local Definition R (c : C) := lim (LA _ (QT c)).

Local Definition lambda (c : C) : cone (QT c) (R c) := limCone (LA _ (QT c)).

Local Definition Rmor_cone (c c' : C) (g : C⟦c,c'⟧) : cone (QT c') (R c).
Proof.
use mk_cone.
- intro m1f1.
  transparent assert (m1gf1 : (c ↓ K)).
  { mkpair.
    + apply (pr1 m1f1).
    + apply (g ;; pr2 m1f1). }
  exact (coneOut (lambda c) m1gf1).
- intros x y f; simpl in *.
  transparent assert (e : ((c ↓ K) ⟦ pr1 x,, g ;; pr2 x, pr1 y,, g ;; pr2 y ⟧)).
  { mkpair.
    + apply (pr1 f).
    + abstract (now rewrite <- assoc, (pr2 f)). }
  exact (coneOutCommutes (lambda c) _ _ e).
Defined.

Local Definition Rmor (c c' : C) (g : C⟦c,c'⟧) : A⟦R c,R c'⟧.
Proof.
use limArrow.
apply (Rmor_cone _ _ g).
Defined.

Local Definition R_data : functor_data C A := R,,Rmor.

Local Definition R_functor : functor C A.
Proof.
apply (tpair _ R_data).
mkpair.
- intros c; simpl.
  apply pathsinv0, limArrowUnique.
  intro c'; simpl.
  rewrite !id_left.
  now destruct c'.
- intros c c' c'' f f'; simpl.
  apply pathsinv0, limArrowUnique.
intros x.
simpl.
unfold lambda.
rewrite <- assoc.
unfold Rmor.
simpl.
etrans.
apply maponpaths.
apply (limArrowCommutes (LA _ (QT c'')) (R c') (Rmor_cone c' c'' f')).
etrans.
apply (@limArrowCommutes _ _ _ (LA _ (QT c')) (R c) (Rmor_cone c c' f) (pr1 x,,f' ;; pr2 x)).
destruct x.
rewrite <- assoc.
apply idpath.
Defined.

Local Definition eps (n : M) : A⟦R_functor (K n),T n⟧ :=
  coneOut (lambda (K n)) (n,,identity (K n)).

End fix_T.

Lemma foo : GlobalRightKanExtensionExists _ _ K _ hsD hsE.
Admitted.

Lemma cocont_pre_composition_functor:
  is_cocont (pre_composition_functor _ _ E hsD hsE K).
Proof.
apply left_adjoint_cocont.
- apply foo.
- apply functor_category_has_homsets.
- apply functor_category_has_homsets.
Qed.

Lemma omega_cocont_pre_composition_functor (hsD : has_homsets D) (hsE : has_homsets E) :
  omega_cocont (pre_composition_functor _ _ E hsD hsE K).
Proof.
intros c L ccL.
apply cocont_pre_composition_functor.
Defined.

End rightkanextension.

Section lambdacalculus.


Definition option_functor : [HSET,HSET,has_homsets_HSET].
Proof.
apply coproduct_functor.
apply CoproductsHSET.
apply (constant_functor _ _ unitHSET).
apply functor_identity.
Defined.

(* TODO: package omega cocont functors *)
Definition LambdaFunctor : functor [HSET,HSET,has_homsets_HSET] [HSET,HSET,has_homsets_HSET].
Proof.
eapply sum_of_functors.
  apply (Coproducts_functor_precat _ _ CoproductsHSET).
  apply (constant_functor [HSET, HSET, has_homsets_HSET] [HSET, HSET, has_homsets_HSET] (functor_identity HSET)).
eapply sum_of_functors.
  apply (Coproducts_functor_precat _ _ CoproductsHSET).
  (* app *)
  eapply functor_composite.
    apply delta_functor.
    apply binproduct_functor.
    apply (Products_functor_precat _ _ ProductsHSET).
(* lam *)
apply (pre_composition_functor _ _ _ _ _ option_functor).
Defined.

(* Bad approach *)
(* Definition Lambda : functor [HSET,HSET,has_homsets_HSET] [HSET,HSET,has_homsets_HSET]. *)
(* Proof. *)
(* eapply functor_composite. *)
(*   apply delta_functor. *)
(* eapply functor_composite. *)
(*   eapply product_of_functors. *)
(*     apply functor_identity. *)
(*     apply delta_functor. *)
(* eapply functor_composite. *)
(*   eapply product_of_functors. *)
(*     apply (constant_functor [HSET, HSET, has_homsets_HSET] [HSET, HSET, has_homsets_HSET] (functor_identity HSET)). *)
(*     eapply product_of_functors. *)
(*       apply delta_functor. *)

Lemma omega_cocont_LambdaFunctor : omega_cocont LambdaFunctor.
Proof.
apply omega_cocont_sum_of_functors.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply functor_category_has_homsets.
  apply omega_cocont_constant_functor.
  apply functor_category_has_homsets.
apply omega_cocont_sum_of_functors.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply functor_category_has_homsets.
  apply omega_cocont_functor_composite.
  apply functor_category_has_homsets.
  apply omega_cocont_delta_functor.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply omega_cocont_binproduct_functor.
  apply functor_category_has_homsets.
  admit.
apply omega_cocont_pre_composition_functor.
Admitted.

End lambdacalculus.