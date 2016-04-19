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

Local Definition Rmor (c c' : C) (g : C⟦c,c'⟧) : A⟦R c,R c'⟧ :=
  limArrow (LA (c' ↓ K) (QT c')) (R c) (Rmor_cone c c' g).

Local Definition R_data : functor_data C A := R,,Rmor.
Local Lemma R_is_functor : is_functor R_data.
Proof.
split.
- intros c; simpl.
  apply pathsinv0, limArrowUnique.
  intro c'; simpl; rewrite !id_left.
  now destruct c'.
- intros c c' c'' f f'; simpl.
  apply pathsinv0, limArrowUnique; intros x; simpl.
  rewrite <- assoc; etrans.
  apply maponpaths, (limArrowCommutes _ _ (Rmor_cone c' c'' f')).
  etrans.
  apply (limArrowCommutes _ _ (Rmor_cone c c' f) (pr1 x,,f' ;; pr2 x)).
  destruct x.
  now rewrite <- assoc.
Qed.

Local Definition R_functor : functor C A := tpair _ R_data R_is_functor.

Local Definition eps_n (n : M) : A⟦R_functor (K n),T n⟧ :=
  coneOut (lambda (K n)) (n,,identity (K n)).

(* TODO: Move to comma category file? *)
Local Definition Kid n : K n ↓ K := (n,, identity (K n)).

Local Lemma eps_is_nat_trans : is_nat_trans (functor_composite_data K R_data) T eps_n.
Proof.
intros n n' h; simpl.
eapply pathscomp0.
apply (limArrowCommutes (LA (K n' ↓ K) (QT (K n'))) (R (K n))
       (Rmor_cone (K n) (K n') (# K h)) (Kid n')).
unfold eps_n; simpl.
transparent assert (v : (K n ↓ K)).
{ apply (n',, # K h ;; identity (K n')). }
transparent assert (e : (K n ↓ K ⟦ Kid n, v ⟧)).
{ mkpair.
  + apply h.
  + abstract (now rewrite id_left, id_right).
}
now apply pathsinv0; eapply pathscomp0; [apply (coneOutCommutes (lambda (K n)) _ _ e)|].
Qed.

Local Definition eps : [M,A,hsA]⟦functor_composite K R_functor,T⟧ :=
  tpair _ eps_n eps_is_nat_trans.

End fix_T.

Lemma RightKanExtension_from_limits : GlobalRightKanExtensionExists _ _ K _ hsC hsA.
Proof.
unfold GlobalRightKanExtensionExists.
use adjunction_from_partial.
- apply R_functor.
- apply eps.
- intros T S α; simpl in *.

transparent assert (cc : (forall c, cone (QT T c) (S c))).
{ intro c.
  use mk_cone.
  + intro mf; apply (# S (pr2 mf) ;; α (pr1 mf)).
  + abstract (intros fm fm' h; simpl; rewrite <- assoc;
              eapply pathscomp0; [apply maponpaths, (pathsinv0 (nat_trans_ax α _ _ (pr1 h)))|];
              simpl; rewrite assoc, <- functor_comp; apply cancel_postcomposition, maponpaths, (pr2 h)).
}
transparent assert (σ : (forall c, A ⟦ S c, R T c ⟧)).
{ intro c; apply (limArrow _ _ (cc c)). }


set (lambda' := fun c' mf' => limOut (LA (c' ↓ K) (QT T c')) mf').
assert (H : forall c c' (g : C ⟦ c, c' ⟧) (mf' : c' ↓ K),
  (# S g ;; σ c' ;; lambda' _ mf' = σ c ;; Rmor T c c' g ;; lambda' _ mf')).
{
intros c c' g; simpl.
set (H1 := limArrowCommutes (LA (c' ↓ K) (QT T c')) (S c') (cc c')).
set (H3 := limArrowCommutes (LA (c' ↓ K) (QT T c')) (R T c) (Rmor_cone T c c' g)).
simpl in *.
intros mf'.
eapply pathscomp0.
Focus 2.
eapply pathsinv0.
rewrite <- assoc.
eapply maponpaths.
apply (H3 mf').
clear H3.
rewrite <- assoc.
eapply pathscomp0.
eapply maponpaths.
apply (H1 mf').
rewrite assoc.
rewrite <- functor_comp.
unfold σ.
set (H2 := limArrowCommutes (LA (c ↓ K) (QT T c)) (S c) (cc c)).
set (mf := tpair _ (pr1 mf') (g ;; pr2 mf') : c ↓ K).
apply pathsinv0.
eapply pathscomp0.
apply (H2 mf).
apply idpath.
}

assert (HHH : is_nat_trans S (R_data T) σ).
{
intros c c' g; simpl.

unfold lambda' in H.
transparent assert (ccc : (cone (QT T c') (S c))).
  use mk_cone.
    intro mf'.
    apply (σ c ;; Rmor T c c' g ;; limOut (LA (c' ↓ K) (QT T c')) mf').
  abstract (intros u v e; simpl; rewrite <- !assoc;
  apply maponpaths, maponpaths, (limOutCommutes (LA (c' ↓ K) (QT T c')) u v e)).
rewrite (limArrowUnique (LA (c' ↓ K) (QT T c')) _ ccc (# S g ;; σ c') (H _ _ _)).
apply pathsinv0, limArrowUnique.
intro mf'.
apply idpath.
}

mkpair.
+ mkpair.
* apply (tpair _ σ HHH).
*
apply (nat_trans_eq hsA); intro n; cbn.
unfold σ.
unfold eps_n.
simpl.
transparent assert (temp : (pr1 (pr1 K) n ↓ K)).
mkpair.
apply n.
apply identity.
apply pathsinv0.
generalize (limArrowCommutes  (LA (pr1 (pr1 K) n ↓ K) (QT T (pr1 (pr1 K) n))) (S (pr1 (pr1 K) n)) (cc (pr1 (pr1 K) n)) temp).
simpl.
now rewrite functor_id, id_left.
+ intro x.
apply subtypeEquality.
intros xx.
apply isaset_nat_trans.
apply hsA.
apply subtypeEquality.
intros xx.
apply isaprop_is_nat_trans.
apply hsA.
simpl.
apply funextsec.
intro c.
unfold is_nat_trans in HHH.
simpl in HHH.
unfold Rmor in HHH.
simpl in HHH.
simpl.
apply limArrowUnique.
intros u.
cbn.
destruct x.
simpl.
assert (lol : α (pr1 u) =
      nat_trans_comp (functor_composite_data K S)
        (functor_composite_data K (R_data T)) T (pre_whisker (pr1 K) t)
        (eps T) (pr1 u)).
  now rewrite p.
rewrite lol.
simpl.
unfold eps_n.
destruct u.
simpl in *.
generalize (nat_trans_ax t _ _ p0).
simpl.
intro HHHHH.
apply pathsinv0.
eapply pathscomp0.
rewrite assoc.
eapply cancel_postcomposition.
apply HHHHH.
rewrite <- !assoc.
apply maponpaths.
unfold Rmor.
transparent assert (apa : (K t0 ↓ K)).
  mkpair. apply t0. apply identity.
set (AA := limArrowCommutes (LA (K t0 ↓ K) (QT T (K t0))) (R T c) (Rmor_cone T c (K t0) p0) apa).
simpl in AA; rewrite id_right in AA.
apply AA.
Defined.

Lemma cocont_pre_composition_functor:
  is_cocont (pre_composition_functor _ _ _ hsC hsA K).
Proof.
apply left_adjoint_cocont.
- apply RightKanExtension_from_limits.
- apply functor_category_has_homsets.
- apply functor_category_has_homsets.
Qed.

Lemma omega_cocont_pre_composition_functor :
  omega_cocont (pre_composition_functor _ _ _ hsC hsA K).
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
  apply has_exponentials_functor_HSET.
  apply has_homsets_HSET.
apply omega_cocont_pre_composition_functor.
apply cats_LimsHSET.
Defined.

End lambdacalculus.