(**
“Displayed equivalences” of displayed (pre)categories
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.

(*
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
*)
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Section Auxiliary.

End Auxiliary.

(* TODO: move somewhere.  Not sure where? [Constructions]? *)
Section Essential_Surjectivity.

Definition fiber_functor_ess_split_surj
    {C C' : category} {D} {D'}
    {F : functor C C'} (FF : disp_functor F D D')
    (H : disp_functor_ff FF)
    {X : disp_functor_ess_split_surj FF}
    {Y : is_op_isofibration D}
  (* TODO: change to [is_isofibration], once [is_isofibration_iff_is_op_isofibration] is provided *)
    (x : C)
  : ∏ yy : D'[{F x}], ∑ xx : D[{x}],
                iso (fiber_functor FF _ xx) yy.
Proof.
  intro yy.
  set (XR := X _ yy).
  destruct XR as [c'' [i [xx' ii]]].
  set (YY := Y _ _ i xx').
  destruct YY as [ dd pe ].
  use tpair.
  - apply dd.
  -
    (* now need disp_functor_on_iso_disp *)
    set (XR := disp_functor_on_iso_disp FF pe).
    set (XR' := iso_inv_from_iso_disp XR).
    (* now need composition of iso_disps *)
    apply  (invweq (iso_disp_iso_fiber _ _ _ _)).
    set (XRt := iso_disp_comp XR' ii).
    transparent assert (XH :
           (iso_comp (iso_inv_from_iso (functor_on_iso F i))
             (functor_on_iso F i) = identity_iso _ )).
    { apply eq_iso. cbn. simpl. unfold precomp_with.
      etrans. apply maponpaths_2. apply id_right.
      etrans. eapply pathsinv0. apply functor_comp.
      etrans. Focus 2. apply functor_id.
      apply maponpaths. apply iso_after_iso_inv.
   }
    set (XRT := transportf (λ r, iso_disp r (FF x dd) yy )
                           XH).
    apply XRT.
    assumption.
Defined.

End Essential_Surjectivity.

(** * General definition of displayed adjunctions and equivalences *)

Section disp_adjunction.

Definition disp_adjunction_data {C C' : category} (A : adjunction_data C C')
           (F := left_functor A) (G := right_functor A)
           (eta := adjunit A) (eps := adjcounit A)
           (D : disp_cat C) (D' : disp_cat C') : UU
  := ∑ (FF : disp_functor F D D') (GG : disp_functor G D' D),
     (disp_nat_trans eta (disp_functor_identity _ )
                     (disp_functor_composite FF GG))
       ×
       (disp_nat_trans eps (disp_functor_composite GG FF) (disp_functor_identity _ )).

Section notation.

Context {C C' : category} {A : adjunction_data C C'}
        {D D'} (X : disp_adjunction_data A D D').
Definition left_adj_over : disp_functor _ _ _ := pr1 X.
Definition right_adj_over : disp_functor _ _ _ := pr1 (pr2 X).
Definition unit_over : disp_nat_trans _ _ _ := pr1 (pr2 (pr2 X)).
Definition counit_over : disp_nat_trans _ _ _ := pr2 (pr2 (pr2 X)).

End notation.

(* TODO: upstream *)
Definition adjunction (A B : precategory) : UU
  := ∑ X : adjunction_data A B, form_adjunction' X.
Coercion data_from_adjunction {A B} (X : adjunction A B)
  : adjunction_data _ _ := pr1 X.
Coercion are_adjoints_from_adjunction {A B} (X : adjunction A B)
  : are_adjoints (left_functor X) (right_functor X).
Proof.
  exists (adjunit X,,adjcounit X).
  exists (pr1 (pr2 X)).
  exact (pr2 (pr2 X)).
Defined.

(* TODO: upstream *)
Definition adjunitiso {A B : precategory} (X : equivalence_of_precats A B)
           (a : A) : iso a (right_functor X (left_functor X a)).
Proof.
  use isopair.
  - exact (adjunit X a).
  - exact (pr1 (pr2 X) a).
Defined.
Definition adjcounitiso {A B : precategory} (X : equivalence_of_precats A B)
           (b : B) : iso (left_functor X (right_functor X b)) b.
Proof.
  use isopair.
  - exact (adjcounit X b).
  - exact (pr2 (pr2 X) b).
Defined.



Definition triangle_1_over_statement
           {C C' : category} {A : adjunction C C'}
           {D D'} (X : disp_adjunction_data A D D')
           (FF := left_adj_over X)
           (ηη := unit_over X)
           (εε := counit_over X) : UU
  := ∏ x xx, #FF (ηη x xx) ;;  εε _ (FF _ xx)
             = transportb _ (triangle_id_left_ad A x ) (id_disp _) .

Definition triangle_2_over_statement
           {C C' : category} {A : adjunction C C'}
           {D D'} (X : disp_adjunction_data A D D')
           (GG := right_adj_over X)
           (ηη := unit_over X)
           (εε := counit_over X) : UU
  := ∏ x xx, ηη _ (GG x xx) ;; # GG (εε _ xx)
           = transportb _ (triangle_id_right_ad A _ ) (id_disp _).

Definition disp_adjunction {C C' : category} (A : adjunction C C') D D' : UU
  := ∑ X : disp_adjunction_data A D D',
           triangle_1_over_statement X × triangle_2_over_statement X.

Coercion adj_over_data_from_adj_over (C C' : category) (A : adjunction C C')
         D D' (X : disp_adjunction A D D') : disp_adjunction_data _ _ _ := pr1 X.

Definition form_equiv {C C' : category} (A : equivalence_of_precats C C') {D D'}
           (X : disp_adjunction_data A D D') : UU
  := ∏ x xx, is_iso_disp (adjunitiso A x) (unit_over X x xx)
     ×
     ∏ x xx, is_iso_disp (adjcounitiso A x) (counit_over X x xx).


End disp_adjunction.




(** * Main definitions *)

(** ** Adjunctions *)
Section Adjunctions.

(** In general, one can define displayed equivalences/adjunctions over any equivalences/adjunctions between the bases (and probably more generally still).  For now we just give the case over a single base precategory — i.e. over an identity functor.

We give the “bidirectional” version first, and then the “handed” versions afterwards, with enough coercions between the two to (hopefully) make it easy to work with both versions. *)

(* TODO: consider carefully the graph of coercions in this section; make them more systematic, and whatever we decide on, DOCUMENT the system clearly. *)

Definition disp_adjunction_id_data {C} (D D' : disp_cat C) : UU
:= ∑ (FF : disp_functor (functor_identity _) D D')
     (GG : disp_functor (functor_identity _) D' D),
     (disp_nat_trans (nat_trans_id _)
            (disp_functor_identity _) (disp_functor_composite FF GG))
   × (disp_nat_trans (nat_trans_id _ )
            (disp_functor_composite GG FF) (disp_functor_identity _)).

(* TODO: consider naming of these access functions *)
Definition left_adj_over_id {C} {D D' : disp_cat C}
  (A : disp_adjunction_id_data D D')
  : disp_functor _ D D'
:= pr1 A.
Coercion left_adj_over_id
  : disp_adjunction_id_data >-> disp_functor.

Definition right_adj_over_id {C} {D D' : disp_cat C}
  (A : disp_adjunction_id_data D D')
  : disp_functor _ D' D
:= pr1 (pr2 A).

Definition unit_over_id {C} {D D' : disp_cat C}
  (A : disp_adjunction_id_data D D')
:= pr1 (pr2 (pr2 A)).

Definition counit_over_id {C} {D D' : disp_cat C}
  (A : disp_adjunction_id_data D D')
:= pr2 (pr2 (pr2 A)).

(** Triangle identies for an adjunction *)

(** Note: the statements of these axioms include [_statement_] to distinguish them from the _instances_ of these statements given by the access functions of [form_adjunction].

This roughly follows the pattern of [univalenceStatement], [funextfunStatement], etc., but departs from it slightly to follow our more general convention of using underscores instead of camelcase.
*)


Definition triangle_1_statement_over_id  {C} {D D' : disp_cat C}
    (A : disp_adjunction_id_data D D')
    (FF := left_adj_over_id A)
    (η := unit_over_id A)
    (ε := counit_over_id A)
  : UU
:= ∏ x xx, #FF ( η x xx) ;;  ε _ (FF _ xx)
            = transportb _ (id_left _ ) (id_disp _) .

Definition triangle_2_statement_over_id  {C} {D D' : disp_cat C}
    (A : disp_adjunction_id_data D D')
    (GG := right_adj_over_id A)
    (η := unit_over_id A)
    (ε := counit_over_id A)
  : UU
:= ∏ x xx, η _ (GG x xx) ;; # GG (ε _ xx)
           = transportb _ (id_left _ ) (id_disp _).

Definition form_disp_adjunction_id {C} {D D' : disp_cat C}
    (A : disp_adjunction_id_data D D')
  : UU
:= triangle_1_statement_over_id A × triangle_2_statement_over_id A.

Definition disp_adjunction_id {C} (D D' : disp_cat C) : UU
:= ∑ A : disp_adjunction_id_data D D', form_disp_adjunction_id A.

Definition data_of_disp_adjunction_id {C} {D D' : disp_cat C}
  (A : disp_adjunction_id D D')
:= pr1 A.
Coercion data_of_disp_adjunction_id
  : disp_adjunction_id >-> disp_adjunction_id_data.

Definition triangle_1_over_id {C} {D D' : disp_cat C}
  (A : disp_adjunction_id D D')
:= pr1 (pr2 A).

Definition triangle_2_over_id {C} {D D' : disp_cat C}
  (A : disp_adjunction_id D D')
:= pr2 (pr2 A).

(** The “left-handed” version: right adjoints to a given functor *)

(** The terminology is difficult to choose here: the proposition “F is a left adjoint” is the same as the type of “right adjoints to F”, so should this type be called something more like [left_adjoint F] or [right_adjoint F]?

Our choice here does _not_ agree with that of the base UniMath category theory library. TODO: consider these conventions, and eventually harmonise them by changing it either here or in UniMath. *)

Definition right_adjoint_over_id_data {C} {D D' : disp_cat C}
  (FF : disp_functor (functor_identity _) D D') : UU
:= ∑ (GG : disp_functor (functor_identity _) D' D),
     (disp_nat_trans (nat_trans_id _)
            (disp_functor_identity _) (disp_functor_composite FF GG))
   × (disp_nat_trans (nat_trans_id _ )
            (disp_functor_composite GG FF) (disp_functor_identity _)).

Definition functor_of_right_adjoint_over_id {C} {D D' : disp_cat C}
  {FF : disp_functor _ D D'}
  (GG : right_adjoint_over_id_data FF)
:= pr1 GG.
Coercion functor_of_right_adjoint_over_id
  : right_adjoint_over_id_data >-> disp_functor.

Definition adjunction_of_right_adjoint_over_id_data {C} {D D' : disp_cat C}
    {FF : disp_functor _ D D'}
    (GG : right_adjoint_over_id_data FF)
  : disp_adjunction_id_data D D'
:= (FF,, GG).
Coercion adjunction_of_right_adjoint_over_id_data
  : right_adjoint_over_id_data >-> disp_adjunction_id_data.

Definition right_adjoint_of_disp_adjunction_id_data {C} {D D' : disp_cat C}
    (A : disp_adjunction_id_data D D')
  : right_adjoint_over_id_data A
:= pr2 A.

Definition right_adjoint_over_id {C} {D D' : disp_cat C}
  (FF : disp_functor (functor_identity _) D D') : UU
:= ∑ GG : right_adjoint_over_id_data FF,
   form_disp_adjunction_id GG.

Definition data_of_right_adjoint_over_id {C} {D D' : disp_cat C}
  {FF : disp_functor _ D D'}
  (GG : right_adjoint_over_id FF)
:= pr1 GG.
Coercion data_of_right_adjoint_over_id
  : right_adjoint_over_id >-> right_adjoint_over_id_data.

Definition adjunction_of_right_adjoint_over_id {C} {D D' : disp_cat C}
    {FF : disp_functor _ D D'}
    (GG : right_adjoint_over_id FF)
  : disp_adjunction_id D D'
:= (adjunction_of_right_adjoint_over_id_data GG ,, pr2 GG).

Definition right_adjoint_of_disp_adjunction_id {C} {D D' : disp_cat C}
    (A : disp_adjunction_id D D')
  : right_adjoint_over_id A
:= (right_adjoint_of_disp_adjunction_id_data A,, pr2 A).

(* TODO: add the dual-handedness version, i.e. indexed over GG instead of FF. *)
End Adjunctions.

Section Equivalences.
(** ** Equivalences (adjoint and quasi) *)

Definition form_equiv_over_id {C} {D D' : disp_cat C}
    (A : disp_adjunction_id_data D D')
    (η := unit_over_id A)
    (ε := counit_over_id A)
  : UU
:= (∏ x xx, is_iso_disp (identity_iso _ ) (η x xx))
 × (∏ x xx, is_iso_disp (identity_iso _ ) (ε x xx)).

Definition is_iso_unit_over_id {C} {D D' : disp_cat C}
  {A : disp_adjunction_id_data D D'}
  (E : form_equiv_over_id A)
:= pr1 E.

Definition is_iso_counit_over_id {C} {D D' : disp_cat C}
  {A : disp_adjunction_id_data D D'}
  (E : form_equiv_over_id A)
:= pr2 E.

Definition equiv_over_id {C} (D D' : disp_cat C) : UU
:= ∑ A : disp_adjunction_id D D', form_equiv_over_id A.

Definition adjunction_of_equiv_over_id {C} {D D' : disp_cat C}
  (A : equiv_over_id D D')
:= pr1 A.
Coercion adjunction_of_equiv_over_id
  : equiv_over_id >-> disp_adjunction_id.

Definition axioms_of_equiv_over_id {C} {D D' : disp_cat C}
  (A : equiv_over_id D D')
:= pr2 A.
Coercion axioms_of_equiv_over_id
  : equiv_over_id >-> form_equiv_over_id.

Definition is_equiv_over_id {C} {D D' : disp_cat C}
  (FF : disp_functor (functor_identity _) D D') : UU
:= ∑ GG : right_adjoint_over_id FF,
   form_equiv_over_id GG.

Definition right_adjoint_of_is_equiv_over_id {C} {D D' : disp_cat C}
  {FF : disp_functor _ D D'}
  (E : is_equiv_over_id FF)
:= pr1 E.
Coercion right_adjoint_of_is_equiv_over_id
  : is_equiv_over_id >-> right_adjoint_over_id.

Definition equiv_of_is_equiv_over_id {C} {D D' : disp_cat C}
    {FF : disp_functor _ D D'}
    (E : is_equiv_over_id FF)
  : equiv_over_id D D'
:= (adjunction_of_right_adjoint_over_id E ,, pr2 E).
Coercion equiv_of_is_equiv_over_id
  : is_equiv_over_id >-> equiv_over_id.
(* Again, don’t worry about the ambiguous path generated here. *)

Definition is_equiv_of_equiv_over_id {CC} {DD DD' : disp_cat CC}
    (E : equiv_over_id DD DD')
  : is_equiv_over_id E
:= (right_adjoint_of_disp_adjunction_id E,, axioms_of_equiv_over_id E).

(* TODO: right-handed versions *)

(* TODO: [quasi_equiv_over_id] (without triangle identities). *)

(** ** Lemmas on the triangle identities *)

Local Open Scope hide_transport_scope.

Lemma triangle_2_from_1_for_equiv_over_id
  {C} {D D' : disp_cat C}
  (A : disp_adjunction_id_data D D')
  (E : form_equiv_over_id A)
: triangle_1_statement_over_id A -> triangle_2_statement_over_id A.
Proof.
  destruct A as [FF [GG [η ε]]].
  destruct E as [Hη Hε]; cbn in Hη, Hε.
  unfold triangle_1_statement_over_id, triangle_2_statement_over_id; cbn.
  intros T1 x yy.
  (* Algebraically, this goes as follows:
  η G ; G ε
  = G ε^ ; η^ G ; η G ; G ε ; η G ; G ε          [by inverses, 1]
  = G ε^ ; η^ G ; η G ; η G F G ; G F G ε ; G ε  [by naturality, 2]
  = G ε^ ; η^ G ; η G ; η G F G ; G ε F G ; G ε  [by naturality, 3]
  = G ε^ ; η^ G ; η G ; G F η G ; G ε F G ; G ε  [by naturality, 4]
  = G ε^ ; η^ G ; η G ; G (F η ; ε F ) G ; G ε   [by functoriality, 5]
  = G ε^ ; η^ G ; η G ; G ε                      [by T1, 6]
  = 1                                            [by inverses, 7]

  It’s perhaps most readable when written in string diagrams. *)
  etrans. apply id_left_disp_var.
  etrans. eapply transportf_bind.
    eapply cancel_postcomposition_disp.
    etrans. eapply transportf_transpose. apply @pathsinv0.
      refine (iso_disp_after_inv_mor _).
      refine (disp_functor_on_is_iso_disp GG _).
      apply Hε. (*1a*)
    eapply transportf_bind.
    eapply cancel_postcomposition_disp.
    etrans. apply id_right_disp_var.
    eapply transportf_bind.
    etrans. eapply cancel_precomposition_disp.
    eapply transportf_transpose. apply @pathsinv0.
      refine (iso_disp_after_inv_mor _).
      apply (Hη). (*1b*)
    eapply transportf_bind, assoc_disp.
  etrans. eapply transportf_bind.
    etrans. apply assoc_disp_var.
    eapply transportf_bind.
    etrans. apply assoc_disp_var.
    eapply transportf_bind.
    eapply cancel_precomposition_disp.
    etrans. eapply cancel_precomposition_disp.
      etrans. apply assoc_disp.
      eapply transportf_bind.
      etrans. eapply cancel_postcomposition_disp.
        exact (disp_nat_trans_ax η (# GG (ε x yy))). (*2*)
      eapply transportf_bind.
      etrans. apply assoc_disp_var.
      eapply transportf_bind.
      eapply cancel_precomposition_disp.
      cbn.
      etrans. eapply transportf_transpose.
        apply @pathsinv0, (disp_functor_comp GG).
      eapply transportf_bind.
      etrans. apply maponpaths.
        apply (disp_nat_trans_ax ε). (*3*)
      cbn.
      etrans. apply (disp_functor_transportf _ GG).
      eapply transportf_bind.
      apply (disp_functor_comp GG).
    eapply transportf_bind.
    etrans. apply assoc_disp.
    eapply transportf_bind.
    etrans. eapply cancel_postcomposition_disp.
      apply (disp_nat_trans_ax η (η x (GG x yy))). (*4*)
    cbn.
    eapply transportf_bind.
    etrans. apply assoc_disp_var.
    eapply transportf_bind.
    eapply cancel_precomposition_disp.
    etrans. apply assoc_disp.
    eapply transportf_bind.
    etrans. eapply cancel_postcomposition_disp.
      etrans. eapply transportf_transpose.
        apply @pathsinv0, (disp_functor_comp GG). (*5*)
      eapply transportf_bind.
      etrans. apply maponpaths, T1. (*6*)
      etrans. apply (disp_functor_transportf _ GG).
      eapply transportf_bind. apply (disp_functor_id GG).
    eapply transportf_bind. apply id_left_disp.
  etrans. eapply transportf_bind.
    etrans. apply assoc_disp_var.
    eapply transportf_bind.
    etrans. eapply cancel_precomposition_disp.
      etrans. apply assoc_disp.
      eapply transportf_bind.
      etrans. eapply cancel_postcomposition_disp.
        exact (iso_disp_after_inv_mor _). (*7a*)
      eapply transportf_bind. apply id_left_disp.
    apply maponpaths. exact (iso_disp_after_inv_mor _). (*7b*)
  etrans. apply transport_f_f.
  unfold transportb. apply maponpaths_2, homset_property.
Time Qed.
(* TODO: [Qed.] takes about 30sec!  [etrans_dep] + [etrans_disp] make it shorter and more readable (see commit 7c1f411a), but make the typechecking time even worse. *)

Lemma triangle_1_from_2_for_equiv_over_id
  {C} {D D' : disp_cat C}
  (A : disp_adjunction_id_data D D')
  (E : form_equiv_over_id A)
: triangle_2_statement_over_id A -> triangle_1_statement_over_id A.
Proof.
  (* dual to previous lemma *)
Abort.

(* TODO: adjointification of a quasi-equivalence. *)

End Equivalences.

(** * Constructions on and of equivalences *)

(** ** Full + faithful + ess split => equivalence *)
Section Equiv_from_ff_plus_ess_split.
(* TODO: consider naming throughout this section!  Especially: anything with [ses] should be fixed. *)

Context {C : category} {D' D : disp_cat C}
        (FF : disp_functor (functor_identity _) D' D)
        (FF_split : disp_functor_disp_ess_split_surj FF)
        (FF_ff : disp_functor_ff FF).

(** *** Utility lemmas from fullness+faithfulness *)

(* TODO: inline throughout? *)
Let FFweq {x y} xx yy (f : x --> y) := disp_functor_ff_weq _ FF_ff xx yy f.
Let FFinv {x y} {xx} {yy} {f}
  := @disp_functor_ff_inv _ _ _ _ _ _ FF_ff x y xx yy f.

(* TODO: once [disp_functor_ff_transportf_gen] is done, replace this with that. *)
Lemma FFinv_transportf
    {x y : C} {f f' : x --> y} (e : f = f')
    {xx : D' x} {yy : D' y} (ff : FF _ xx -->[f] FF _ yy)
  : FFinv (transportf _ e ff) = transportf _ e (FFinv ff).
Proof.
  destruct e. apply idpath.
Qed.

(* TODO: once more general [disp_functor_ff_reflects_isos] is done, kill this and replace it with that. *)
Definition disp_functor_id_ff_reflects_isos
  {x y} {xx : D' x} {yy : D' y} {f : iso x y}
  (ff : xx -->[ f ] yy) (isiso: is_iso_disp f (# FF ff))
  : is_iso_disp _ ff.
Proof.
  set (FFffinv := inv_mor_disp_from_iso isiso).
  set (ffinv := FFinv FFffinv).
  exists ffinv.
  split.
  - unfold ffinv. unfold FFffinv.
    apply (invmaponpathsweq (@FFweq _ _ _ _ _ )). cbn.
    etrans. apply (disp_functor_comp FF).
    etrans. apply maponpaths. apply maponpaths_2. apply (homotweqinvweq (@FFweq _ _ _ _ _ )).
    etrans. apply maponpaths. apply iso_disp_after_inv_mor.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply (disp_functor_transportf _ FF).
    etrans. apply maponpaths. apply disp_functor_id.
    etrans. apply transport_f_f.
    apply maponpaths_2. apply homset_property.
  - apply (invmaponpathsweq (@FFweq _ _ _ _ _ )). cbn.
    etrans. apply (disp_functor_comp FF).
    etrans. apply maponpaths. apply maponpaths. apply (homotweqinvweq (@FFweq _ _ _ _ _ )).
    etrans. apply maponpaths. apply inv_mor_after_iso_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply (disp_functor_transportf _ FF).
    etrans. apply maponpaths. apply disp_functor_id.
    etrans. apply transport_f_f.
    apply maponpaths_2. apply homset_property.
Qed.

Definition FFinv_on_iso_is_iso   {x y} {xx : D' x} {yy : D' y} {f : iso x y}
  (ff : FF _ xx -->[ f ] FF _ yy) (Hff: is_iso_disp f ff)
  : is_iso_disp _ (FFinv ff).
Proof.
  apply disp_functor_id_ff_reflects_isos.
  use (transportf _ _ Hff).
  apply @pathsinv0. use homotweqinvweq.
Qed.

(** *** Converse functor *)

(* TODO: does [Local Definition] actually keep it local?  It seems not — e.g. [Print GG_data] still works after the section closes. Is there a way to actually keep them local?  If not, find less generic names for [GG] and its components. *)
Local Definition GG_data : disp_functor_data (functor_identity _ ) D D'.
Proof.
  use tpair.
  + intros x xx. exact (pr1 (FF_split x xx)).
  + intros x y xx yy f ff; simpl.
    set (Hxx := FF_split x xx).
    set (Hyy := FF_split y yy).
    apply FFinv.
    refine (transportf (mor_disp _ _) _ _). Focus 2.
    exact ((pr2 Hxx ;; ff) ;; inv_mor_disp_from_iso (pr2 Hyy)).
    cbn. etrans. apply id_right. apply id_left.
Defined.

Local Lemma GG_ax : disp_functor_axioms GG_data.
Proof.
  split; simpl.
  + intros x xx.
    apply invmap_eq. cbn.
    etrans. Focus 2. apply @pathsinv0, (disp_functor_id FF).
    etrans. apply maponpaths.
      etrans. apply maponpaths_2, id_right_disp.
      etrans. apply mor_disp_transportf_postwhisker.
      apply maponpaths, (inv_mor_after_iso_disp (pr2 (FF_split _ _))).
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    unfold transportb. apply maponpaths_2, homset_property.
  + intros x y z xx yy zz f g ff gg.
    apply invmap_eq. cbn.
    etrans. Focus 2. apply @pathsinv0.
      etrans. apply (disp_functor_comp FF).
      etrans. apply maponpaths.
        etrans. apply maponpaths; use homotweqinvweq.
        apply maponpaths_2; use homotweqinvweq.
      etrans. apply maponpaths.
        etrans. apply mor_disp_transportf_prewhisker.
        apply maponpaths.
        etrans. apply mor_disp_transportf_postwhisker.
        apply maponpaths.
        etrans. apply maponpaths, assoc_disp_var.
        etrans. apply mor_disp_transportf_prewhisker.
        apply maponpaths.
        etrans. apply assoc_disp.
        apply maponpaths.
        etrans. apply maponpaths_2.
          etrans. apply assoc_disp_var.
          apply maponpaths.
          etrans. apply maponpaths.
            exact (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
          etrans. apply mor_disp_transportf_prewhisker.
          etrans. apply maponpaths, id_right_disp.
          apply transport_f_f.
        etrans. apply maponpaths_2, transport_f_f.
        apply mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      (* A trick to hide the huge equality term: *)
      apply maponpaths_2. shelve.
    etrans. apply maponpaths.
      etrans. apply maponpaths_2, assoc_disp.
      etrans. apply mor_disp_transportf_postwhisker.
      apply maponpaths. apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    apply maponpaths_2, homset_property.
    Unshelve. Focus 2. apply idpath.
Qed.

Definition GG : disp_functor _ _ _ := (_ ,, GG_ax).

Definition ε_ses_ff_data
  : disp_nat_trans_data (nat_trans_id _ )
      (disp_functor_composite GG FF) (disp_functor_identity _ )
:= λ x xx, (pr2 (FF_split x xx)).

Lemma ε_ses_ff_ax : disp_nat_trans_axioms ε_ses_ff_data.
Proof.
  intros x y f xx yy ff. cbn. unfold ε_ses_ff_data.
  etrans. apply maponpaths_2; use homotweqinvweq.
  etrans. apply mor_disp_transportf_postwhisker.
  etrans. apply maponpaths.
    etrans. apply assoc_disp_var.
    apply maponpaths.
    etrans. apply maponpaths.
      apply (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
    etrans. apply mor_disp_transportf_prewhisker.
    apply maponpaths, id_right_disp.
  etrans. apply transport_f_f.
  etrans. apply transport_f_f.
  etrans. apply transport_f_f.
  unfold transportb. apply maponpaths_2, homset_property.
Qed.

Definition ε_ses_ff
  : disp_nat_trans (nat_trans_id _ )
      (disp_functor_composite GG FF) (disp_functor_identity _ )
:= (ε_ses_ff_data,, ε_ses_ff_ax).

Definition η_ses_ff_data
  : disp_nat_trans_data (nat_trans_id _)
      (disp_functor_identity _ ) (disp_functor_composite FF GG).
Proof.
  intros x xx. cbn.
  apply FFinv.
  exact (inv_mor_disp_from_iso (pr2 (FF_split _ _))).
Defined.

Definition η_ses_ff_ax
  : disp_nat_trans_axioms η_ses_ff_data.
Proof.
  intros x y f xx yy ff. cbn. unfold η_ses_ff_data.
  (* This feels a bit roundabout.  Can it be simplified? *)
  apply @pathsinv0.
  etrans. eapply maponpaths.
    etrans. apply @pathsinv0, disp_functor_ff_inv_compose.
    apply maponpaths.
    etrans. apply mor_disp_transportf_prewhisker.
    apply maponpaths.
    etrans. apply assoc_disp.
    apply maponpaths.
    etrans. apply maponpaths_2.
      etrans. apply assoc_disp.
      apply maponpaths.
      etrans.
        apply maponpaths_2, (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths, id_left_disp.
      apply transport_f_f.
    etrans. apply maponpaths_2, transport_f_f.
    apply mor_disp_transportf_postwhisker.
  etrans. apply maponpaths.
    etrans. apply maponpaths.
      etrans. apply transport_f_f.
      apply transport_f_f.
    apply FFinv_transportf.
  etrans. apply transport_f_f.
  apply transportf_comp_lemma_hset.
    apply homset_property.
  etrans. apply (disp_functor_ff_inv_compose _ FF_ff).
  apply maponpaths_2, homotinvweqweq.
Qed.

Definition η_ses_ff
  : disp_nat_trans (nat_trans_id _)
      (disp_functor_identity _ ) (disp_functor_composite FF GG)
:= (_ ,, η_ses_ff_ax).

Definition GGεη : right_adjoint_over_id_data FF
  := (GG,, (η_ses_ff,, ε_ses_ff)).

Lemma form_equiv_GGεη : form_equiv_over_id GGεη.
Proof.
  split; intros x xx; cbn.
  - unfold η_ses_ff_data.
    apply (@FFinv_on_iso_is_iso _ _ _ _ (identity_iso _)).
    eapply is_iso_disp_independent_of_is_iso.
    exact (@is_iso_inv_from_iso_disp _ _ _ _ (identity_iso _) _ _ _).
  - unfold ε_ses_ff_data.
    apply is_iso_disp_from_iso.
Qed.

Lemma tri_1_GGεη : triangle_1_statement_over_id GGεη.
Proof.
  intros x xx; cbn.
  unfold ε_ses_ff_data, η_ses_ff_data.
  etrans. apply maponpaths_2; use homotweqinvweq.
  etrans. exact (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
  apply maponpaths_2, homset_property.
Qed.

Lemma tri_2_GGεη : triangle_2_statement_over_id GGεη.
Proof.
  apply triangle_2_from_1_for_equiv_over_id.
  apply form_equiv_GGεη.
  apply tri_1_GGεη.
Qed.

Theorem is_equiv_from_ff_ess_over_id : is_equiv_over_id FF.
Proof.
  use ((GGεη,, _) ,, _).
  split. apply tri_1_GGεη. apply tri_2_GGεη.
  apply form_equiv_GGεη.
Defined.

End Equiv_from_ff_plus_ess_split.

(** ** Inverses and composition of adjunctions/equivalences *)

Section Nat_Trans_Disp_Inv.

Context {C : category} {D' D : disp_cat C}
        {FF GG : disp_functor (functor_identity _) D' D}
        (alpha : disp_nat_trans (nat_trans_id _ ) FF GG)
        (Ha : ∏ x xx, is_iso_disp (identity_iso _ ) (alpha x xx)).

(*
Lemma inv_ax : disp_nat_trans_axioms
    (λ (x : C) (xx : D' x), @inv_mor_disp_from_iso _ _ _ _ (identity_iso _ ) _  _ _ (Ha x xx)).
*)

Local Lemma inv_ax : @disp_nat_trans_axioms C C (functor_identity_data C)
    (functor_identity_data C) (@nat_trans_id C C (functor_identity_data C))
    D' D GG FF
    (λ (x : C) (xx : D' x),
     @inv_mor_disp_from_iso C D ((functor_identity C) x)
       ((functor_identity C) x) (@identity_iso C ((functor_identity C) x))
       (FF x xx) (GG x xx) (alpha x xx) (Ha x xx)).
Proof.
     intros x y f xx yy ff.
    apply pathsinv0.
    apply transportf_pathsinv0.
    apply pathsinv0.
    set (XR := @iso_disp_precomp).
    specialize (XR _ _ _ _ (identity_iso _ ) _ _ (alpha x xx ,, Ha x xx) ).
    match goal with |[|- ?EE = _ ] => set (E := EE) end. cbn in E.
    specialize (XR _ (identity x · f) (FF y yy)).
    set (R := weqpair _ XR).
    apply (invmaponpathsweq R).
    unfold R. unfold E. cbn.
    etrans. apply assoc_disp.
    etrans. apply maponpaths. apply maponpaths_2.
            apply (inv_mor_after_iso_disp (Ha x xx)).
    etrans. apply maponpaths.
            apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans.            apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths.
            apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2.
            apply (disp_nat_trans_ax_var alpha).
    etrans. apply maponpaths.
            apply mor_disp_transportf_postwhisker.
    etrans.    apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths.
            apply (inv_mor_after_iso_disp (Ha _ _ )).
    etrans. apply maponpaths.
            apply mor_disp_transportf_prewhisker.

     etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f.
    apply maponpaths_2.
    apply homset_property.
Qed.

Local Definition inv : disp_nat_trans (nat_trans_id _ ) GG FF.
Proof.
  use tpair.
  - intros x xx.
    apply (inv_mor_disp_from_iso (Ha _ _ )).
  - apply inv_ax.
Defined.

End Nat_Trans_Disp_Inv.

Section Displayed_Equiv_Inv.

Context {C : category} {D' D : disp_cat C}
        (FF : disp_functor (functor_identity _) D' D)
        (isEquiv : is_equiv_over_id FF).

Let GG : disp_functor _ D D' := right_adjoint_of_is_equiv_over_id isEquiv.
Let η : disp_nat_trans (nat_trans_id (functor_identity C))
                       (disp_functor_identity D')
                       (disp_functor_composite FF GG)
  := unit_over_id isEquiv.

Let ε :  disp_nat_trans
           (nat_trans_id (functor_identity C))
           (disp_functor_composite GG FF)
           (disp_functor_identity D)
  := counit_over_id isEquiv.

Definition η_inv : disp_nat_trans (nat_trans_id (functor_identity C))
    (disp_functor_identity D) (disp_functor_composite GG FF).
Proof.
  apply (inv ε).
  apply (is_iso_counit_over_id isEquiv).
Defined.

Definition ε_inv :
 disp_nat_trans
    (nat_trans_id
       (functor_identity C))
    (disp_functor_composite FF GG) (disp_functor_identity D').
Proof.
  apply (inv η). cbn.
  apply (is_iso_unit_over_id isEquiv).
Defined.

Definition inv_adjunction_data : disp_adjunction_id_data D D'.
Proof.
  exists GG.
  exists FF.
  exists η_inv.
  exact ε_inv.
Defined.

Lemma form_equiv_inv_adjunction_data : form_equiv_over_id inv_adjunction_data.
Proof.
  cbn. use tpair.
    + intros. cbn.
      set (XR:= @is_iso_inv_from_is_iso_disp).
      specialize (XR _ D _  _ _ _ _ _ (  is_iso_counit_over_id (pr2 isEquiv) x xx)).
      cbn in XR.
      eapply is_iso_disp_independent_of_is_iso.
      apply XR.
    + cbn. intros.
      set (XR:= @is_iso_inv_from_is_iso_disp).
      specialize (XR _ D' _  _ _ _ _ _ (  is_iso_unit_over_id (pr2 isEquiv) x xx)).
      cbn in XR.
      eapply is_iso_disp_independent_of_is_iso.
      apply XR.
Qed.

Lemma inv_triangle_1_statement_over_id
  : triangle_1_statement_over_id inv_adjunction_data.
Proof.
  intros x xx. cbn.
        set (XR:= @iso_disp_precomp).
        set (Gepsxxx := (#GG (ε x xx))).
        set (RG := @disp_functor_on_is_iso_disp _ _ (functor_identity C)).
        specialize (RG _ _ GG).
        specialize (RG _ _ _ _ (identity_iso _ )  (ε x xx)).
        specialize (RG (is_iso_counit_over_id (pr2 isEquiv) x xx)).
        transparent assert (Ge : (iso_disp (identity_iso x)
                                  (GG _ (FF _ (GG _ xx))) (GG _ xx))).
        { apply (iso_disp_pair (f:=identity_iso _ ) Gepsxxx).
          eapply is_iso_disp_independent_of_is_iso.
          apply RG.
        }

        match goal with |[|- ?EE = _ ] => set (E := EE) end. cbn in E.
        specialize (XR _ _ _ _ _ _ _ Ge).
        specialize (XR _ (identity x · identity x ) (GG x xx)).
        apply (invmaponpathsweq (weqpair _ XR)).
        unfold E; clear E.
        cbn.
        clear RG XR Ge.
        unfold Gepsxxx.
        etrans. apply assoc_disp.
        etrans. apply maponpaths. apply maponpaths_2.
                eapply pathsinv0. apply (disp_functor_comp_var GG).
        etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths. apply maponpaths_2.
                apply maponpaths.
                apply (inv_mor_after_iso_disp (is_iso_counit_over_id (pr2 isEquiv) x xx)).
        etrans. apply maponpaths. apply maponpaths_2.
                apply (disp_functor_transportf _ GG).
        etrans. apply maponpaths. apply  mor_disp_transportf_postwhisker.
        etrans. apply ( transport_f_f _ _ _ _ ).
        etrans. apply maponpaths. apply maponpaths_2.
                apply (disp_functor_id GG).
        etrans. apply maponpaths. apply  mor_disp_transportf_postwhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths. apply id_left_disp.
        etrans. apply transport_f_f.

        match goal with |[|- transportf _ ?EE _ = _ ] => generalize EE end.
        intro EE.

        set (XR:= @iso_disp_precomp).
        set (etaGxxx := η _ (GG x xx)).
        transparent assert (Ge : (iso_disp (identity_iso x)
                                  (GG _ xx) (GG _ (FF _ (GG _ xx))) )).
        { apply (iso_disp_pair (f:=identity_iso _ ) etaGxxx).
          eapply is_iso_disp_independent_of_is_iso.
          apply (is_iso_unit_over_id (pr2 isEquiv) ).
        }

        match goal with |[|- ?EE = _ ] => set (E := EE) end. cbn in E.
        specialize (XR _ _ _ _ _ _ _ Ge).
        specialize (XR _ (identity x · (identity x · identity x) )  (GG x xx)).
        apply (invmaponpathsweq (weqpair _ XR)).

        cbn. unfold etaGxxx.
        unfold E.
        clear E. clear XR Ge etaGxxx.
        clear Gepsxxx.

        etrans. apply  mor_disp_transportf_prewhisker.
        etrans. apply maponpaths.
           apply (inv_mor_after_iso_disp (is_iso_unit_over_id (pr2 isEquiv) x _ )).
        etrans. apply transport_f_f.
        apply pathsinv0.
        etrans. apply maponpaths. apply  mor_disp_transportf_prewhisker.
        etrans. apply mor_disp_transportf_prewhisker.
        etrans. apply maponpaths.
                apply maponpaths. apply id_right_disp.
        etrans. apply maponpaths. apply  mor_disp_transportf_prewhisker.
        etrans. apply transport_f_f.
        set (XR := triangle_2_over_id isEquiv).
        unfold triangle_1_statement_over_id in XR.
        cbn in XR.
        etrans. apply maponpaths. apply XR.
        etrans. apply transport_f_f.
        apply maponpaths_2.
        apply homset_property.
Qed.

Lemma inv_triangle_2_statement_over_id
  : triangle_2_statement_over_id inv_adjunction_data.
Proof.
  apply triangle_2_from_1_for_equiv_over_id.
  - apply form_equiv_inv_adjunction_data.
  - apply inv_triangle_1_statement_over_id.
Qed.


Definition equiv_inv : is_equiv_over_id GG.
Proof.
  use tpair.
  - use tpair.
    + exact (FF,, (η_inv,, ε_inv)).
    + use tpair. cbn. apply inv_triangle_1_statement_over_id.
      apply inv_triangle_2_statement_over_id.
  - apply form_equiv_inv_adjunction_data.
Defined.

End Displayed_Equiv_Inv.

Section Displayed_Equiv_Compose.

(* TODO: give composites of displayed equivalences. *)

End Displayed_Equiv_Compose.

(** ** Induced adjunctions/equivalences of fiber precats *)
Section Equiv_Fibers.

Context {C : category}.

Definition fiber_is_left_adj {D D' : disp_cat C}
  {FF : disp_functor (functor_identity _) D D'}
  (EFF : right_adjoint_over_id FF)
  (c : C)
: is_left_adjoint (fiber_functor FF c).
Proof.
  destruct EFF as [[GG [η ε]] axs]; simpl in axs.
  exists (fiber_functor GG _).
  exists (fiber_nat_trans η _,,
          fiber_nat_trans ε _).
  use tpair; cbn.
  + unfold triangle_1_statement.
    intros d; cbn.
    set (thisax := pr1 axs c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    use (@maponpaths_2 _ _ _ _ _ (paths_refl _)).
    apply homset_property.
  + unfold triangle_2_statement.
    intros d; cbn.
    set (thisax := pr2 axs c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    use (@maponpaths_2 _ _ _ _ _ (paths_refl _)).
    apply homset_property.
Defined.

Definition fiber_equiv {D D' : disp_cat C}
  {FF : disp_functor (functor_identity _) D D'}
  (EFF : is_equiv_over_id FF)
  (c : C)
: adj_equivalence_of_precats (fiber_functor FF c).
Proof.
  exists (fiber_is_left_adj EFF c).
  destruct EFF as [[[GG [η ε]] tris] isos]; cbn in isos; cbn.
  use tpair.
  + intros d.
    apply is_iso_fiber_from_is_iso_disp.
    apply (is_iso_unit_over_id isos).
  + intros d.
    apply is_iso_fiber_from_is_iso_disp.
    apply (is_iso_counit_over_id isos).
Defined.

End Equiv_Fibers.

(* *)
