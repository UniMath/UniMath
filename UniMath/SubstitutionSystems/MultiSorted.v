(**

This file contains a fomalization of multisorted binding signatures:

- Definition of multisorted binding signatures ([MultiSortedSig])
- Construction of a functor from a multisorted binding signature
  ([MultiSortedSigToFunctor])
- Proof that the functor obtained from a multisorted binding signature
  is omega-cocontinuous ([is_omega_cocont_MultiSortedSigToFunctor])


Written by: Anders Mörtberg, 2016. The formalization follows a note
written by Benedikt Ahrens and Ralph Matthes, and is also inspired by
discussions with them and Vladimir Voevodsky.

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.SubstitutionSystems.Signatures.
(* Require Import UniMath.SubstitutionSystems.SignatureExamples. *)
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
(* Require Import UniMath.SubstitutionSystems.LiftingInitial_alt. *)
(* Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems. *)

Local Notation "[ C , D ]" := (functor_Precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "C / X" := (slicecat_ob C X).
Local Notation "C / X" := (slice_precat_data C X).
Local Notation "C / X" := (slice_precat C X (homset_property C)).
Local Notation "C / X ⟦ a , b ⟧" := (slicecat_mor C X a b) (at level 50, format "C / X ⟦ a , b ⟧").

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variables (sort : hSet).

Let SET : Precategory := (HSET,,has_homsets_HSET).

Local Definition SET_over_sort : Precategory.
Proof.
exists (SET / sort).
now apply has_homsets_slice_precat.
Defined.

Let post_comp := post_composition_functor (SET / sort) _ _
                   (homset_property SET_over_sort) has_homsets_HSET.

(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU :=
  ∑ (I : hSet), I → list (list sort × sort) × sort.

Definition ops (M : MultiSortedSig) : hSet := pr1 M.
Definition arity (M : MultiSortedSig) : ops M → list (list sort × sort) × sort :=
  λ x, pr2 M x.

(** * Construction of an endofunctor on [SET/sort,SET/sort] from a multisorted signature *)
Section functor.

Local Definition proj_fun (s : sort) : SET / sort -> SET :=
  λ p, hfiber_hSet (pr2 p) s.

Local Definition proj_functor (s : sort) : functor (SET / sort) SET.
Proof.
mkpair.
- exists (proj_fun s).
  intros X Y f p.
  exists (pr1 f (pr1 p)).
  abstract (now destruct f as [h hh]; destruct p as [x hx]; simpl in *; rewrite <- hx, hh).
- abstract (split; [intros X|intros X Y Z f g];
            apply funextsec; intro p; apply subtypeEquality; trivial;
            intros x; apply setproperty).
Defined.

(** The left adjoint to the proj_functor *)
Local Definition hat_functor (t : sort) : functor SET (SET / sort).
Proof.
mkpair.
- mkpair.
  + intro A; apply (A,,λ _, t).
  + intros A B f; apply (tpair _ f), idpath.
- abstract (now split; [intros A|intros A B C f g];
            apply subtypeEquality; try (intro x; apply has_homsets_HSET)).
Defined.

Local Definition option_fun : sort -> SET / sort -> SET / sort.
Proof.
simpl; intros s Xf.
mkpair.
+ exists (hfiber (sumofmaps (pr2 Xf) (termfun s)) s).
  abstract (apply isaset_total2;
              [apply isasetcoprod; [apply setproperty| apply isasetunit]
              |intros []; simpl; intro x; apply isasetaprop, setproperty]).
+ intros F; induction (pr1 F) as [t|t].
  - apply (pr2 Xf t).
  - apply s.
Defined.

Local Definition option_functor_data (s : sort) : functor_data (SET / sort) (SET / sort).
Proof.
exists (option_fun s).
intros X Y f.
mkpair.
- intros F.
  mkpair.
  * induction (pr1 F) as [t|t]; [apply (ii1 (pr1 f t)) | apply (ii2 t)].
  * abstract (induction F as [[t|t] h]; trivial; rewrite <- h;
              apply (toforallpaths _ _ _ (! pr2 f) t)).
- abstract (apply funextsec; intros [[t|t] h]; trivial; apply (toforallpaths _ _ _ (pr2 f) t)).
Defined.

Local Lemma is_functor_option_functor (s : sort) : is_functor (option_functor_data s).
Proof.
split; simpl.
+ intros X; apply (eq_mor_slicecat has_homsets_HSET), funextsec; intros [t Ht].
  apply subtypeEquality; [intros x; apply setproperty|]; simpl.
  now induction t.
+ intros X Y Z f g; apply (eq_mor_slicecat has_homsets_HSET), funextsec; intros [t Ht].
  apply subtypeEquality; [intros x; apply setproperty|]; simpl.
  now induction t.
Qed.

Local Definition option_functor (s : sort) : functor (SET / sort) (SET / sort) :=
  tpair _ _ (is_functor_option_functor s).

(** option_functor for lists (also called option in the note) *)
Local Definition option_list (xs : list sort) : functor (SET / sort) (SET / sort).
Proof.
use (foldr _ _ xs).
+ intros s F.
  apply (functor_composite (option_functor s) F).
+ apply functor_identity.
Defined.

(** Define a functor F^(l,t)(X) := proj_functor(t) ∘ X ∘ option_functor(l) *)
Local Lemma exp_functor (lt : list sort × sort) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET].
Proof.
eapply functor_composite.
- apply (pre_composition_functor _ _ _ (homset_property SET_over_sort) _ (option_list (pr1 lt))).
- apply post_comp, (proj_functor (pr2 lt)).
Defined.

(** This defines F^lts where lts is a list of (l,t). Outputs a product of
    functors if the list is nonempty and otherwise the constant functor. *)
Local Definition exp_functor_list (xs : list (list sort × sort)) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET].
Proof.
(* Apply the exp functor to every element of the list *)
set (XS := map exp_functor xs).
(* If the list is empty we output the constant functor *)
set (T := constant_functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET]
                           (constant_functor SET_over_sort HSET TerminalHSET)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
use (foldr1 (fun F G => BinProduct_of_functors _ _ _ F G) T XS).
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Local Definition hat_exp_functor_list (xst : list (list sort × sort) × sort) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET_over_sort].
Proof.
eapply functor_composite.
+ apply (exp_functor_list (pr1 xst)).
+ eapply post_composition_functor.
  apply (hat_functor (pr2 xst)).
Defined.

(** The function from multisorted signatures to functors *)
Definition MultiSortedSigToFunctor (M : MultiSortedSig) :
  functor [SET_over_sort,SET_over_sort] [SET_over_sort,SET_over_sort].
Proof.
use (coproduct_of_functors (ops M)).
+ apply Coproducts_functor_precat.
  apply Coproducts_slice_precat.
  apply CoproductsHSET, setproperty.
+ intros op.
  apply (hat_exp_functor_list (arity M op)).
Defined.

End functor.

(** * Proof that the functor obtained from a multisorted signature is omega-cocontinuous *)
Section omega_cocont.

(** The object (1,λ _,s) in SET/sort *)
Local Definition constHSET_slice (s : sort) : SET / sort.
Proof.
exists (TerminalObject TerminalHSET); simpl.
apply (λ x, s).
Defined.

(** The proj functor is naturally isomorphic to the following functor which is a left adjoint: *)
Local Definition proj_functor' (s : sort) : functor (SET / sort) SET :=
  functor_composite
     (constprod_functor1 (BinProducts_HSET_slice sort) (constHSET_slice s))
     (slicecat_to_cat has_homsets_HSET sort).

Local Lemma nat_trans_proj_functor (s : sort) : nat_trans (proj_functor' s) (proj_functor s).
Proof.
use mk_nat_trans.
- simpl; intros x H.
  exists (pr2 (pr1 H)).
  apply (!pr2 H).
- intros x y f.
  apply funextsec; intro w.
  apply subtypeEquality; trivial.
  intro z; apply setproperty.
Defined.

Local Lemma is_iso_nat_trans_proj_functor (s : sort) :
  @is_iso [SET/sort,SET] _ _ (nat_trans_proj_functor s).
Proof.
use is_iso_qinv.
+ use mk_nat_trans.
  - simpl; intros x xy.
    exists (tt,,pr1 xy).
    apply (!pr2 xy).
  - abstract (intros X Y f; apply funextsec; intros x;
              apply subtypeEquality; trivial; intros w; apply setproperty).
+ abstract (split;
  [ apply subtypeEquality; [intros x; apply isaprop_is_nat_trans, has_homsets_HSET|];
    apply funextsec; intro x; apply funextsec; intro y; cbn;
    now rewrite pathsinv0inv0; induction y as [[[] y2] y3]
  | apply (nat_trans_eq has_homsets_HSET); simpl; intros x;
    apply funextsec; intros z; simpl in *;
    now apply subtypeEquality; trivial; intros w; apply setproperty]).
Defined.

Local Lemma is_left_adjoint_proj_functor' (s : sort) : is_left_adjoint (proj_functor' s).
Proof.
use is_left_adjoint_functor_composite.
- apply has_exponentials_HSET_slice.
- apply is_left_adjoint_slicecat_to_cat_HSET.
Defined.

Local Lemma is_left_adjoint_proj_functor (s : sort) : is_left_adjoint (proj_functor s).
Proof.
apply (is_left_adjoint_iso _ _ _ (_,,is_iso_nat_trans_proj_functor s)).
apply is_left_adjoint_proj_functor'.
Defined.

Local Lemma is_omega_cocont_post_comp_proj (s : sort) :
  is_omega_cocont (post_comp (proj_functor s)).
Proof.
apply is_omega_cocont_post_composition_functor.
apply is_left_adjoint_proj_functor.
Defined.

(** The hat_functor is left adjoint to proj_functor *)
Local Lemma is_left_adjoint_hat (s : sort) : is_left_adjoint (hat_functor s).
Proof.
exists (proj_functor s).
use mk_are_adjoints.
+ use mk_nat_trans.
  - intros X; simpl; intros x; apply (x,,idpath s).
  - intros X Y f; simpl; apply funextsec; intro x; cbn.
    now apply subtypeEquality; trivial; intros y; apply setproperty.
+ use mk_nat_trans.
  - intros X; simpl in *.
    mkpair; simpl.
    * intros H; apply (pr1 H).
    * abstract (apply funextsec; intro x; apply (! pr2 x)).
  - now intros X Y f; apply (eq_mor_slicecat has_homsets_HSET).
+ split.
  - now intros X; apply (eq_mor_slicecat has_homsets_HSET).
  - intros X; apply funextsec; intro x.
    now apply subtypeEquality; trivial; intros x'; apply setproperty.
Defined.

Local Lemma is_omega_cocont_exp_functor (a : list sort × sort)
  (H : Colims_of_shape nat_graph SET_over_sort) :
  is_omega_cocont (exp_functor a).
Proof.
apply is_omega_cocont_functor_composite.
+ apply functor_category_has_homsets.
+ apply is_omega_cocont_pre_composition_functor, H.
+ apply is_omega_cocont_post_comp_proj.
Defined.

Local Lemma is_omega_cocont_exp_functor_list (xs : list (list sort × sort))
  (H : Colims_of_shape nat_graph SET_over_sort) :
  is_omega_cocont (exp_functor_list xs).
Proof.
induction xs as [[|n] xs].
- induction xs.
  apply is_omega_cocont_constant_functor, functor_category_has_homsets.
- induction n as [|n IHn].
  + induction xs as [m []].
    apply is_omega_cocont_exp_functor, H.
  + induction xs as [m [k xs]].
    apply is_omega_cocont_BinProduct_of_functors; try apply homset_property.
    * apply BinProducts_functor_precat, BinProducts_slice_precat, PullbacksHSET.
    * apply is_omega_cocont_constprod_functor1; try apply functor_category_has_homsets.
      apply has_exponentials_functor_HSET, homset_property.
    * apply is_omega_cocont_exp_functor, H.
    * apply (IHn (k,,xs)).
Defined.

Local Lemma is_omega_cocont_post_comp_hat_functor (s : sort) :
  is_omega_cocont (post_composition_functor SET_over_sort  _ _
       (homset_property SET) (homset_property SET_over_sort)
       (hat_functor s)).
Proof.
apply is_omega_cocont_post_composition_functor, is_left_adjoint_hat.
Defined.

Local Lemma is_omega_cocont_hat_exp_functor_list (xst : list (list sort × sort) × sort)
  (H : Colims_of_shape nat_graph SET_over_sort) :
  is_omega_cocont (hat_exp_functor_list xst).
Proof.
apply is_omega_cocont_functor_composite.
+ apply functor_category_has_homsets.
+ apply is_omega_cocont_exp_functor_list, H.
+ apply is_omega_cocont_post_comp_hat_functor.
Defined.

(** The functor obtained from a multisorted binding signature is omega-cocontinuous *)
Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig)
  (Heq : isdeceq (ops M)) (H : Colims_of_shape nat_graph SET_over_sort) :
  is_omega_cocont (MultiSortedSigToFunctor M).
Proof.
apply is_omega_cocont_coproduct_of_functors; try apply homset_property.
+ apply Products_functor_precat, Products_HSET_slice.
+ apply Heq.
+ intros op; apply is_omega_cocont_hat_exp_functor_list, H.
Defined.

End omega_cocont.
End MBindingSig.


(** Alternative version using [X,SET] instead of SET/X below. There is no proof that the
    functor we obtain using this approach is omega-cocontinuous yet. *)
Module alt.

Require Import UniMath.CategoryTheory.DiscretePrecategory.
Require Import UniMath.CategoryTheory.EquivalencesExamples.

(** * Definition of multisorted binding signatures *)
Section MBindingSig.

Variables (sort : UU) (eq : isdeceq sort). (* Can we eliminate this assumption? *)
Variables (C : Precategory) (BP : BinProducts C) (BC : BinCoproducts C) (TC : Terminal C).

(** Define the discrete category of sorts *)
Let sort_cat : precategory := discrete_precategory sort.

Let hsC : has_homsets C := homset_property C.

(** This represents "sort → C" *)
Let sortToC : Precategory := [sort_cat,C].

Local Lemma has_homsets_sortToC : has_homsets sortToC.
Proof.
apply homset_property.
Qed.

Local Definition BinProductsSortToCToC : BinProducts [sortToC,C].
Proof.
apply (BinProducts_functor_precat _ _ BP).
Defined.

Local Definition mk_sortToC (f : sort → C) : sortToC :=
  functor_discrete_precategory _ _ f.

Local Definition proj_gen_fun (D : precategory) (E : Precategory) (d : D) : functor [D,E] E.
Proof.
mkpair.
+ mkpair.
  - intro f; apply (pr1 f d).
  - simpl; intros a b f; apply (f d).
+ abstract (split; [intro f; apply idpath|intros f g h fg gh; apply idpath]).
Defined.

Local Definition proj_gen {D : precategory} {E : Precategory} : functor D [[D,E],E].
Proof.
mkpair.
+ mkpair.
  - apply proj_gen_fun.
  - intros d1 d2 f.
    mkpair.
    * simpl; intro F; apply (# F f).
    * abstract (intros F G α; simpl in *; apply pathsinv0, (nat_trans_ax α d1 d2 f)).
+ abstract (split;
  [ intros F; simpl; apply nat_trans_eq; [apply homset_property|]; intro G; simpl; apply functor_id
  | intros F G H α β; simpl; apply nat_trans_eq; [apply homset_property|];
    intro γ; simpl; apply functor_comp ]).
Defined.

(** Given a sort s this applies the sortToC to s and returns C *)
Definition projSortToC (s : sort) : functor sortToC C.
Proof.
apply proj_gen_fun.
apply s.
Defined.

(** Definition of multi sorted signatures *)
Definition MultiSortedSig : UU :=
  ∏ (s : sort), ∑ (I : UU), (I → list (list sort × sort)). (* × (isaset I). *)

Definition indices (M : MultiSortedSig) : sort → UU := fun s => pr1 (M s).

Definition args (M : MultiSortedSig) (s : sort) : indices M s → list (list sort × sort) :=
  pr2 (M s).

Local Notation "'1'" := (TerminalObject TC).
Local Notation "a ⊕ b" := (BinCoproductObject _ (BC a b)) (at level 50).

(* Code for option as a function, below is the definition as a functor *)
Local Definition option_fun : sort -> sortToC -> sortToC.
Proof.
intros s f.
apply mk_sortToC; intro t.
induction (eq s t) as [H|H].
- apply (pr1 f t ⊕ 1).
- apply (pr1 f t).
Defined.

(* The function part of Definition 3 *)
Local Definition option_functor_data  (s : sort) : functor_data sortToC sortToC.
Proof.
mkpair.
+ apply (option_fun s).
+ intros F G α.
  mkpair.
  * simpl; intro t.
    induction (eq s t) as [p|p]; simpl; clear p.
    { apply (BinCoproductOfArrows _ _ _ (α t) (identity _)). }
    { apply α. }
  * abstract (now intros t1 t2 []; cbn; induction (eq s t1); simpl; rewrite id_left, id_right).
Defined.

Local Lemma is_functor_option_functor s : is_functor (option_functor_data s).
Proof.
split.
+ intros F; apply (nat_trans_eq hsC); intro t; simpl.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  now apply pathsinv0, BinCoproductArrowUnique; rewrite id_left, id_right.
+ intros F G H αFG αGH; apply (nat_trans_eq hsC); intro t; simpl.
  induction (eq s t) as [p|p]; trivial; simpl; clear p.
  apply pathsinv0; eapply pathscomp0; [apply precompWithBinCoproductArrow|].
  rewrite !id_left; apply BinCoproductArrowUnique.
  * now rewrite BinCoproductIn1Commutes, assoc.
  * now rewrite BinCoproductIn2Commutes, id_left.
Qed.

(* This is Definition 3 (sorted context extension) from the note *)
Local Definition option_functor (s : sort) : functor sortToC sortToC :=
  tpair _ _ (is_functor_option_functor s).

(* option_functor for lists (also called option in the note) *)
Local Definition option_list (xs : list sort) : functor sortToC sortToC.
Proof.
use (foldr _ _ xs).
+ intros s F.
  apply (functor_composite (option_functor s) F).
+ apply functor_identity.
Defined.

(* This is X^a as a functor between functor categories *)
Local Lemma exp_functor (a : list sort × sort) : functor [sortToC,sortToC] [sortToC,C].
Proof.
eapply functor_composite.
- apply (pre_composition_functor _ _ _ has_homsets_sortToC _ (option_list (pr1 a))).
- apply post_composition_functor, (projSortToC (pr2 a)).
Defined.

(* Lemma is_omega_cocont_exp_functor (a : list sort × sort) *)
(*   (H : Colims_of_shape nat_graph sortToC) : *)
(*   is_omega_cocont (exp_functor a). *)
(* Proof. *)
(* apply is_omega_cocont_functor_composite. *)
(* + apply functor_category_has_homsets. *)
(* + apply is_omega_cocont_pre_composition_functor. *)
(*   apply H. *)
(* + apply is_omega_cocont_post_composition_functor. *)
(*   admit. *)
(* Admitted. *)

(* This defines X^as where as is a list. Outputs a product of functors if the list is nonempty and *)
(* otherwise the constant functor. *)
Local Definition exp_functors (xs : list (list sort × sort)) :
  functor [sortToC,sortToC] [sortToC,C].
Proof.
(* Apply the exp functor to every element of the list *)
set (XS := map exp_functor xs).
(* If the list is empty we output the constant functor *)
set (T := constant_functor [sortToC,sortToC] [sortToC,C]
                           (constant_functor sortToC C TC)).
(* TODO: Maybe use indexed finite products instead of a fold? *)
apply (foldr1 (fun F G => BinProduct_of_functors _ _ BinProductsSortToCToC F G) T XS).
Defined.

(* H follows if C has exponentials? *)
(* Lemma is_omega_cocont_exp_functors (xs : list (list sort × sort)) *)
(*   (H : ∏ x : [sortToC, C], is_omega_cocont (constprod_functor1 BinProductsSortToCToC x)) *)
(*   (H2 : Colims_of_shape nat_graph sortToC) : *)
(*   is_omega_cocont (exp_functors xs). *)
(* Proof. *)
(* destruct xs as [[|n] xs]. *)
(* - destruct xs. *)
(*   apply is_omega_cocont_constant_functor. *)
(*   apply (functor_category_has_homsets sortToC). *)
(* - induction n as [|n IHn]. *)
(*   + destruct xs as [m []]. *)
(*     apply is_omega_cocont_exp_functor, H2. *)
(*   + destruct xs as [m [k xs]]. *)
(*     apply is_omega_cocont_BinProduct_of_functors; try apply homset_property. *)
(*     * now repeat apply BinProducts_functor_precat. *)
(*     * apply H. *)
(*     * apply is_omega_cocont_exp_functor, H2. *)
(*     * apply (IHn (k,,xs)). *)
(* Defined. *)


(* From here on things are not so nice: *)
Local Definition MultiSortedSigToFunctor_helper1 (C1 D E1 : precategory) (E2 : Precategory)
  : functor [E1,[C1,[D,E2]]] [E1,[D,[C1,E2]]].
Proof.
eapply post_composition_functor.
apply functor_cat_swap.
Defined.

(* This lemma is just here to check that the correct sort_cat gets pulled out when reorganizing *)
(*    arguments *)
Local Definition MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (E2 : Precategory) :
  functor [E1,[C1,[D,E2]]] [C1,[D,[E1,E2]]].
Proof.
eapply (functor_composite (functor_cat_swap _ _ _)).
apply MultiSortedSigToFunctor_helper1.
Defined.



(* The above definition might be the same as: *)
(* functor_composite (functor_cat_swap F) functor_cat_swap. *)

(* Local Definition MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (E2 : Precategory) *)
(*   (F : functor E1 [C1,[D,E2]]) : functor C1 [D,[E1,E2]]. *)
(*     functor_composite (functor_cat_swap F) functor_cat_swap. *)


(* Lemma is_omega_cocont_MultiSortedSigToFunctor_helper (C1 D E1 : precategory) (E2 : Precategory) *)
(*   (F : functor E1 [C1,[D,E2]]) (HF : ∏ s, is_omega_cocont (F s)) : *)
(*   is_omega_cocont (MultiSortedSigToFunctor_helper C1 D E1 E2 F). *)
(* Proof. *)
(* apply is_omega_cocont_functor_composite. *)
(* + apply functor_category_has_homsets. *)
(* + admit. *)
(* + apply is_omega_cocont_functor_cat_swap. *)
(* Admitted. *)

(* Local Definition MultiSortedSigToFunctor_helper2 (C1 D E1 : precategory) (E2 : Precategory) : *)
(*   functor [E1,[D,[C1,E2]]] [C1,[D,[E1,E2]]]. *)
(* Proof. *)
(* eapply functor_composite;[apply functor_cat_swap|]. *)
(* eapply functor_composite;[|apply functor_cat_swap]. *)
(* eapply functor_composite; [eapply post_composition_functor; apply functor_cat_swap|]. *)
(* apply functor_identity. *)
(* Defined. *)

Local Definition MultiSortedSigToFunctor_fun (M : MultiSortedSig) (CC : ∏ s, Coproducts (indices M s) C)
  : [sort_cat, [[sortToC, sortToC], [sortToC, C]]].
Proof.
(* As we're defining a functor out of a discrete category it suffices to give a function: *)
apply functor_discrete_precategory; intro s.
use (coproduct_of_functors (indices M s)).
+ apply Coproducts_functor_precat, CC.
+ intros y; apply (exp_functors (args M s y)).
Defined.

(* Lemma is_omega_cocont_MultiSortedSigToFunctor_fun *)
(*   (M : MultiSortedSig) (CC : ∏ s, Coproducts (indices M s) C) *)
(*   (CP : ∏ s, Products (indices M s) C) *)
(*   (hs : ∏ s, isdeceq (indices M s)) *)
(*   (H : ∏ x : [sortToC, C], is_omega_cocont (constprod_functor1 BinProductsSortToCToC x)) *)
(*   (H2 : Colims_of_shape nat_graph sortToC) : *)
(*   ∏ s, is_omega_cocont (pr1 (MultiSortedSigToFunctor_fun M CC) s). *)
(* Proof. *)
(* intros s. *)
(* apply is_omega_cocont_coproduct_of_functors; try apply homset_property. *)
(* + apply Products_functor_precat, Products_functor_precat, CP. *)
(* + apply (hs s). *)
(* + intros y; apply is_omega_cocont_exp_functors. *)
(*   - apply H. *)
(*   - apply H2. *)
(* Defined. *)

(** * The functor constructed from a multisorted binding signature *)
Definition MultiSortedSigToFunctor (M : MultiSortedSig) (CC : ∏ s, Coproducts (indices M s) C) :
  functor [sortToC,sortToC] [sortToC,sortToC].
Proof.
(* First reorganize so that the last sort argument is first: *)
set (F := MultiSortedSigToFunctor_helper [sortToC,sortToC] sortToC sort_cat C).
set (x := MultiSortedSigToFunctor_fun M CC).
apply (F x).
Defined.

(* Lemma is_omega_cocont_MultiSortedSigToFunctor (M : MultiSortedSig) *)
(*   (CC : ∏ s, Coproducts (indices M s) C) *)
(*   (PC : ∏ s, Products (indices M s) C) *)
(*   (Hi : ∏ s, isdeceq (indices M s)) *)
(*   (H : ∏ x : [sortToC, C], is_omega_cocont (constprod_functor1 BinProductsSortToCToC x)) : *)
(*    is_omega_cocont (MultiSortedSigToFunctor M CC). *)
(* Proof. *)
(* apply is_omega_cocont_functor_composite. *)
(* + apply (homset_property [sortToC,sortToC]). *)
(* + simpl. admit. *)
(* + apply is_omega_cocont_functor_cat_swap. *)
(* Admitted. *)

End MBindingSig.
End alt.
