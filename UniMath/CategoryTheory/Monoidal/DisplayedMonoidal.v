(** Displayed monoidal categories

Author: Benedikt Ahrens 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.


Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Notation "C ⊠ C'" := (category_binproduct C C').

Section DispCartProdOfCats.

  Context {C C' : category}
          (D : disp_cat C)
          (D' : disp_cat C').

  Definition disp_binprod_ob_mor : disp_cat_ob_mor (C ⊠ C').
  Proof.
    use tpair.
    - intro cc'. exact (D (pr1 cc') × D' (pr2 cc')).
    - intros aa' bb' xx' yy' fg.
      exact ( (pr1 xx' -->[ pr1 fg ] pr1 yy') × (pr2 xx' -->[ pr2 fg ] pr2 yy' )).
  Defined.

  Definition disp_binprod_id_comp : disp_cat_id_comp _ disp_binprod_ob_mor.
  Proof.
    use tpair.
    - intros x xx.
      use make_dirprod.
      * apply id_disp.
      * apply id_disp.
    - intros aa' bb' cc' ff' gg'  xx' yy' zz' hh' ii'.
      use make_dirprod.
      * apply (comp_disp (pr1 hh') (pr1 ii')).
      * apply (comp_disp (pr2 hh') (pr2 ii')).
  Defined.


  Definition disp_binprod_data : disp_cat_data (C ⊠ C')
    := disp_binprod_ob_mor ,,  disp_binprod_id_comp.


  Lemma disp_binprod_transportf_pr1 (a b : C) (f g : a --> b)
        (a' b' : C') (f' g' : a' --> b')
        (x : D a) (y : D b) (x' : D' a') (y' : D' b')
        (ff : x -->[f] y) (ff' : x' -->[f'] y')
        (e : catbinprodmor f f' = catbinprodmor g g')
    : transportf (mor_disp _ _) (maponpaths pr1 e) ff
      =
      pr1 (transportf (@mor_disp _ disp_binprod_data (a,,a') _ (x,, x') (_,, _)) e (ff,, ff')) .
  Proof.
    induction e.
    apply idpath.
  Qed.


  Lemma disp_binprod_transportf_pr2 (a b : C) (f g : a --> b)
        (a' b' : C') (f' g' : a' --> b')
        (x : D a) (y : D b) (x' : D' a') (y' : D' b')
        (ff : x -->[f] y) (ff' : x' -->[f'] y')
        (e : catbinprodmor f f' = catbinprodmor g g')
    : transportf (mor_disp _ _) (maponpaths (dirprod_pr2) e) ff'
      =
      pr2 (transportf (@mor_disp _ disp_binprod_data (a,,a') _ (x,, x') (_,, _)) e (ff,, ff')) .
  Proof.
    induction e.
    apply idpath.
  Qed.


  Lemma disp_binprod_axioms : disp_cat_axioms _ disp_binprod_data.
  Proof.
    repeat split.
    - intros [a a'] [b b'] [f f'] [x x'] [y y'] [ff ff'].
      simpl in *.
      apply dirprodeq.
      * simpl in *.
        etrans.
        apply id_left_disp.
        etrans.
        2: { apply disp_binprod_transportf_pr1. }
        apply transportf_paths.
        apply C.
      * simpl in *.
        etrans. apply id_left_disp.
        etrans.
        2: { apply disp_binprod_transportf_pr2. }
        apply transportf_paths.
        apply C'.
    - intros [a a'] [b b'] [f f'] [x x'] [y y'] [ff ff'].
      simpl in *.
      apply dirprodeq.
      * simpl in *.
        etrans.
        apply id_right_disp.
        etrans.
        2: { apply disp_binprod_transportf_pr1. }
        apply transportf_paths.
        apply C.
      * simpl in *.
        etrans. apply id_right_disp.
        etrans.
        2: { apply disp_binprod_transportf_pr2. }
        apply transportf_paths.
        apply C'.
    - intros [a a'] [b b'] [c c'] [d d'] [f f'] [g g'] [h h'] [x x'] [y y'] [z z']
             [w w'] [u u'] [v v'] [r r'].
      simpl in *.
      apply dirprodeq.
      * simpl.
        etrans. apply assoc_disp.
        etrans.
        2: { apply disp_binprod_transportf_pr1. }
        apply transportf_paths.
        apply C.
      * simpl.
        etrans. apply assoc_disp.
        etrans.
        2: { apply disp_binprod_transportf_pr2. }
        apply transportf_paths.
        apply C'.
    - intros.
      apply isasetdirprod.
      * apply D.
      * apply D'.
  Qed.

  Definition disp_binprod : disp_cat (C ⊠ C')
    :=  disp_binprod_data ,,  disp_binprod_axioms.

End DispCartProdOfCats.

Notation "D ⊠⊠ D'" := (disp_binprod D D') (at level 60).


Section TotalDispProd.

(**
We can build the total category of a [disp_binprod D D'], or we can take the cartesian product of two total categories.
 *)

 Context {C C' : category}
         (D : disp_cat C)
         (D' : disp_cat C').

 Let T : category := total_category (D ⊠⊠ D').
 Let T' : category := total_category D ⊠ total_category D'.

 Definition reord1_functor_data : functor_data T T'.
 Proof.
   use tpair.
   - intros [[c c'] [d d']].
     exact (make_dirprod (c,,d) (c',,d')).
   - cbn. intros [[a a'] [d d']] [[b b'] [e e']] [[f f'] [g g']].
     exact (make_dirprod (f,,g) (f',,g')).
 Defined.



 Definition reord1_functor_axioms : is_functor reord1_functor_data.
 Proof.
   split.
   - intros a.
     apply idpath.
   - intros a b c f g.
     apply idpath.
 Qed.

 Definition reord1_functor : functor T T' := reord1_functor_data ,, reord1_functor_axioms.

 Definition reord1_hom_inverse (a b : T)
   : T' ⟦ reord1_functor a, reord1_functor b ⟧ → T ⟦ a, b ⟧.
 Proof.
   intros [[c d] [c' d']].
   cbn in *.
   use tpair.
   - exact (make_dirprod c c').
   - cbn. exact (make_dirprod d d').
 Defined.

 Definition fully_faithful_reord1_functor : fully_faithful reord1_functor.
 Proof.
   intros a b.
   use gradth.
   - exact (reord1_hom_inverse a b).
   - intros. apply idpath.
   - intros; apply idpath.
 Defined.

 Definition reord1_ob_inverse : T' → T.
 Proof.
   intros [[c d] [c' d']].
   use tpair.
   - exact (make_dirprod c c').
   - exact (make_dirprod d d').
 Defined.

 Definition is_catiso_reord_functor : is_catiso reord1_functor.
 Proof.
   split.
   - exact fully_faithful_reord1_functor.
   - use gradth.
     + exact reord1_ob_inverse.
     + intro; apply idpath.
     + intro; apply idpath.
 Defined.

 Definition catiso_reord : catiso T T' := _ ,, is_catiso_reord_functor .

End TotalDispProd.


Definition total_bifunctor
           {C D E : category}
           (F : C ⊠ D ⟶ E)
           {DC : disp_cat C}
           {DD : disp_cat D}
           {DE : disp_cat E}
           (FF : disp_functor F (DC ⊠⊠ DD) DE)
  : total_category DC ⊠ total_category DD ⟶ total_category DE
  := inv_catiso (catiso_reord DC DD) ∙ total_functor FF.


Lemma disp_binprod_transportf (C C' : category) (D : disp_cat C) (D' : disp_cat C')
      (a b : C) (a' b' : C') (f g : a --> b) (f' g' : a' --> b')
      (x : D a) (y : D b) (x' : D' a') (y' : D' b')
      (ff : x -->[f] y) (ff' : x' -->[f'] y')
      (e : (f,,f') = (g,, g'))
  : transportf (@mor_disp (C ⊠ C') (disp_binprod D D') (a,,a') (b,,b') (x,,x') (y,,y')) e (ff,, ff')  =
      transportf (mor_disp _ _ ) (maponpaths pr1 e) ff ,, transportf (mor_disp _ _ )  (maponpaths (dirprod_pr2) e) ff'.
Proof.
  induction e.
  apply idpath.
Qed.


Section DispCartProdOfFunctors.

  Context {A A' C C' : category}
          {F : functor A C}
          {F' : functor A' C'}
          {D : disp_cat A}
          {D' : disp_cat A'}
          {E : disp_cat C}
          {E' : disp_cat C'}
          (G : disp_functor F D E)
          (G' : disp_functor F' D' E').

  Definition disp_pair_functor_data
    : disp_functor_data (pair_functor F F') (D ⊠⊠ D') (E ⊠⊠ E').
  Proof.
    use tpair.
    - intros aa' dd'.
      use make_dirprod.
      + use G. apply (pr1 dd').
      + use G'. apply (pr2 dd').
    - cbn. intros aa' aa'' xx' yy' ff' gg'.
      use make_dirprod.
      + apply #G. apply (pr1 gg').
      +  apply #G'. apply (pr2 gg').
  Defined.

  Lemma disp_pair_functor_axioms :
    @disp_functor_axioms (A ⊠ A') (C ⊠ C') (pair_functor F F') _ _ disp_pair_functor_data.
  Proof.
    split.
    - intros [a a'] [d d'].
      apply pathsinv0.
      etrans. { apply disp_binprod_transportf. }
      cbn.
      apply dirprodeq; cbn.
      + apply pathsinv0.
        etrans. apply disp_functor_id.
        apply transportf_paths. apply C.
      + apply pathsinv0.
        etrans. apply disp_functor_id.
        apply transportf_paths. apply C'.
    - intros [a a'] [b b'] [c c'] [w w'] [x x'] [y y'] [f f'] [g g'] [ff ff'] [gg gg'].
      cbn in *.
      apply pathsinv0.
      etrans. { apply disp_binprod_transportf. }
      apply pathsinv0.
      apply dirprodeq; cbn.
      + etrans. apply disp_functor_comp.
        apply transportf_paths. apply C.
      + etrans. apply disp_functor_comp.
        apply transportf_paths. apply C'.
  Qed.

  Definition disp_pair_functor :
    @disp_functor (A ⊠ A') (C ⊠ C')  (pair_functor F F') (D ⊠⊠ D') (E ⊠⊠ E')
    :=  disp_pair_functor_data ,, disp_pair_functor_axioms.

End DispCartProdOfFunctors.

Section DispAssocFunctors.

  Context (A B C : category)
          (DA : disp_cat A)
          (DB : disp_cat B)
          (DC : disp_cat C).

  Definition disp_assoc_data :
    disp_functor_data (precategory_binproduct_assoc A B C)
                      (DA ⊠⊠ (DB ⊠⊠ DC))
                      ((DA ⊠⊠ DB) ⊠⊠ DC).
  Proof.
    use tpair.
    - intros abc dabc.
      exact ( (pr1 dabc,,pr12 dabc) ,, pr22 dabc).
    - intros abc abc' xx yy f g.
      exact ( (pr1 g,,pr12 g) ,, pr22 g).
  Defined.

  (* Make a general lemma that encompasses the two parts here *)
  Lemma disp_assoc_axioms : disp_functor_axioms disp_assoc_data.
  Proof.
    split.
    - intros x xx.
      cbn.
      apply dirprod_paths.
      + cbn.
        apply dirprod_paths.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr1 (DA ⊠⊠ DB) DC). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr1 DA DB). }
          apply pathsinv0.
          apply transportf_set.
          apply A.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr1 (DA ⊠⊠ DB) DC). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr2 DA DB). }
          apply pathsinv0.
          apply transportf_set.
          apply B.
      + cbn.
        etrans.
        2 : { apply (disp_binprod_transportf_pr2 (DA ⊠⊠ DB) DC). }
        apply pathsinv0.
        apply transportf_set.
        apply C.
    - intros.
      cbn.
      apply dirprod_paths.
      + cbn.
        apply dirprod_paths.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr1 (DA ⊠⊠ DB) DC). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr1 DA DB). }
          apply pathsinv0.
          apply transportf_set.
          apply A.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr1 (DA ⊠⊠ DB) DC). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr2 DA DB). }
          apply pathsinv0.
          apply transportf_set.
          apply B.
      + cbn.
        etrans.
        2 : { apply (disp_binprod_transportf_pr2 (DA ⊠⊠ DB) DC). }
        apply pathsinv0.
        apply transportf_set.
        apply C.
  Qed.

  Definition disp_assoc
    : disp_functor (precategory_binproduct_assoc A B C)
                   (DA ⊠⊠ (DB ⊠⊠ DC)) ((DA ⊠⊠ DB) ⊠⊠ DC)
    := _ ,, disp_assoc_axioms.


  Definition disp_unassoc_data :
    disp_functor_data (precategory_binproduct_unassoc A B C)
                      ((DA ⊠⊠ DB) ⊠⊠ DC)
                      (DA ⊠⊠ (DB ⊠⊠ DC)).
  Proof.
    use tpair.
    - intros abc dabc.
      exact ( pr11 dabc,, (pr21 dabc ,, pr2 dabc)).
    - intros abc abc' xx yy f g.
      exact ( pr11 g,, (pr21 g ,, pr2 g)).
  Defined.

  (* Make a general lemma that encompasses the two parts here *)
  Lemma disp_unassoc_axioms : disp_functor_axioms disp_unassoc_data.
  Proof.
    split.
    - intros x xx.
      cbn.
      apply dirprod_paths.
      + cbn.
        etrans.
        2 : { apply (disp_binprod_transportf_pr1 DA (DB ⊠⊠ DC)). }
        apply pathsinv0.
        apply transportf_set.
        apply A.
      + cbn.
        apply dirprod_paths.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr2 DA (DB ⊠⊠ DC) ). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr1 DB DC). }
          apply pathsinv0.
          apply transportf_set.
          apply B.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr2 DA (DB ⊠⊠ DC)). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr2 DB DC). }
          apply pathsinv0.
          apply transportf_set.
          apply C.
    - intros.
      cbn.
      apply dirprod_paths.
      + cbn.
        etrans.
        2 : { apply (disp_binprod_transportf_pr1 DA (DB ⊠⊠ DC)). }
        apply pathsinv0.
        apply transportf_set.
        apply A.
      + cbn.
        apply dirprod_paths.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr2 DA (DB ⊠⊠ DC) ). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr1 DB DC). }
          apply pathsinv0.
          apply transportf_set.
          apply B.
        * cbn.
          etrans.
          2 : { apply maponpaths.
                apply (disp_binprod_transportf_pr2 DA (DB ⊠⊠ DC)). }
          etrans.
          2 : { apply (disp_binprod_transportf_pr2 DB DC). }
          apply pathsinv0.
          apply transportf_set.
          apply C.
  Qed.

  Definition disp_unassoc
    : disp_functor (precategory_binproduct_assoc A B C)
                   (DA ⊠⊠ (DB ⊠⊠ DC)) ((DA ⊠⊠ DB) ⊠⊠ DC)
    := _ ,, disp_assoc_axioms.


End DispAssocFunctors.



Lemma transportf_fst_arg_type
        {A B C : category}
        {DA : disp_cat A}
        {DB : disp_cat B}
        {DC : disp_cat C}
        {F : A ⊠ B ⟶ C}
        (FF : disp_functor F (DA ⊠⊠ DB) DC)
        {a₁ a₂ : A}
        {da₁ : DA a₁}
        {da₂ : DA a₂}
        {f f' : a₁ --> a₂}
        (e : f = f')
        (ff : da₁ -->[f] da₂)
        {b₁ b₂ : B}
        {db₁ : DB b₁}
        {db₂ : DB b₂}
        {g : b₁ --> b₂}
        (gg : db₁ -->[g] db₂)

  : UU.
Proof.
  refine
    (@disp_functor_on_morphisms  _ _ _ _ _ FF (a₁,,b₁) (a₂,,b₂) (da₁,,db₁) (da₂,,db₂) (f',,g) (make_dirprod (transportf (mor_disp da₁ da₂) e ff)
                                                                                                            gg) = _ ).
  set (X := @disp_functor_on_morphisms  _ _ _ _ _ FF (a₁,,b₁) (a₂,,b₂) (da₁,,db₁) (da₂,,db₂) (f,,g) (ff,,gg)).
  refine (transportf _ _ X).
  apply maponpaths.
  apply maponpaths_2.
  apply e.
Defined.

Lemma  transportf_fst_arg
        {A B C : category}
        {DA : disp_cat A}
        {DB : disp_cat B}
        {DC : disp_cat C}
        {F : A ⊠ B ⟶ C}
        (FF : disp_functor F (DA ⊠⊠ DB) DC)
        {a₁ a₂ : A}
        {da₁ : DA a₁}
        {da₂ : DA a₂}
        {f f' : a₁ --> a₂}
        (e : f = f')
        (ff : da₁ -->[f] da₂)
        {b₁ b₂ : B}
        {db₁ : DB b₁}
        {db₂ : DB b₂}
        {g : b₁ --> b₂}
        (gg : db₁ -->[g] db₂)
  : transportf_fst_arg_type FF e ff gg.
Proof.
  unfold transportf_fst_arg_type.
  induction e.
  cbn.
  apply idpath.
Qed.


Section disp_fix_fst_arg.

  Local Notation "( f #, g )" := (catbinprodmor f g).

  Context {A B C : category}
          {DA : disp_cat A}
          {DB : disp_cat B}
          {DC : disp_cat C}
          (F : functor (A ⊠ B) C)
          (FF : disp_functor F (DA ⊠⊠ DB) DC)
          (a : A)
          (da : DA a).


  Definition disp_functor_fix_fst_arg_ob {b : B} (db : DB b) : DC (F _) := FF (a,,b) (da,, db).

  Definition disp_functor_fix_fst_arg_mor {b₁ b₂ : B} {f : b₁ --> b₂} {db₁ : DB b₁} {db₂ : DB b₂} (ff : db₁ -->[f] db₂)
    : FF (a,,b₁) (da,,db₁) -->[ (# F (identity _ #,f))%cat ] FF (a,,b₂) (da,,db₂).
  Proof.
    apply #FF.
    apply (id_disp _ ,, ff).
  Defined.

  Definition disp_functor_fix_fst_arg_data
    : disp_functor_data (functor_fix_fst_arg _ _ _ F a) DB DC.
  Proof.
    exists @disp_functor_fix_fst_arg_ob.
    intros x y xx yy f ff.
    apply disp_functor_fix_fst_arg_mor.
    apply ff.
  Defined.


  Definition disp_functor_fix_fst_arg_axioms
    : disp_functor_axioms disp_functor_fix_fst_arg_data.
  Proof.
    split.
    - intros.
      cbn.
      unfold disp_functor_fix_fst_arg_mor.
      rewrite (@disp_functor_id _ _ _ _ _ FF).
      apply transportf_transpose_right.
      etrans. { apply transport_f_f. }
      apply transportf_set.
      apply C.
    - intros.
      cbn.
      unfold disp_functor_fix_fst_arg_mor.
      apply transportf_transpose_right.
      set (X := @disp_functor_comp_var _ _ _ _ _ FF).
      etrans.
      2 : { apply X. }
      cbn.
      apply transportf_transpose_right.
      etrans. 2 : { apply maponpaths.
                    apply maponpaths_2.
                    eapply pathsinv0.
                    apply id_left_disp. }
            etrans. { apply transport_f_f. }
      apply pathsinv0.
      etrans.
      apply  transportf_fst_arg.
      cbn.
      apply  transportf_transpose_right.
      etrans. apply transport_f_f.
      apply transportf_set.
      apply C.
  Qed.

  Definition disp_functor_fix_fst_arg
    : disp_functor (functor_fix_fst_arg _ _ _ F a) DB DC
    := _ ,, disp_functor_fix_fst_arg_axioms.

End disp_fix_fst_arg.





Definition displayed_tensor
           {C : category}
           (tensor : C ⊠ C ⟶ C)
           (D : disp_cat C)
  : UU
  := disp_functor tensor (disp_binprod D D) D.

Identity Coercion displayed_tensor_to_disp_functor : displayed_tensor >-> disp_functor.

Definition total_tensor
           {C : category}
           (T : C ⊠ C ⟶ C)
           {D : disp_cat C}
           (TT : displayed_tensor T D)
  : total_category D ⊠ total_category D ⟶ total_category D
  := total_bifunctor T TT.


Section section_tensor.


  (**
              TT
    D × D ------------> D
    ∧   ∧               ∧
   S|   |S              |S
    C × C ------------> C
               T
   *)

  Context {C : category}
          {D : disp_cat C}
          (T : C ⊠ C ⟶ C)
          (TT : displayed_tensor T D)
          (S : section_disp D).


  Local Definition make_prodmor
        {a₁ a₂ b₁ b₂ : C}
        (f₁ : a₁ --> b₁)
        (f₂ : a₂ --> b₂)
    : C ⊠ C ⟦ a₁,,a₂ , b₁,,b₂ ⟧
    := (f₁ ,, f₂).

  Local Notation "f ⊠' f'" := (make_prodmor f f') (at level 30).


  Local Definition make_dispprodmor
        {a₁ a₂ b₁ b₂ : C}
        {f₁ : a₁ --> b₁}
        {f₂ : a₂ --> b₂}
        {d₁ : D a₁}
        {d₂ : D a₂}
        {e₁ : D b₁}
        {e₂ : D b₂}
        (ff₁ : d₁ -->[f₁] e₁)
        (ff₂ : d₂ -->[f₂] e₂)
    : @mor_disp _ (D⊠⊠D) (a₁,,a₂) (b₁,,b₂) (d₁ ,, d₂ )  ( e₁ ,, e₂ ) ( f₁ ,, f₂ )
    := ff₁ ,, ff₂.

  Local Notation "f ⊠⊠' f'" := (make_dispprodmor f f') (at level 30).


  (** This is leaving the displayed world, so is only useful for validation *)
  Definition section_functor_pair : functor (C ⊠ C) (total_category D ⊠ total_category D).
  Proof.
    use pair_functor.
    - use section_functor.
      exact S.
    - use section_functor.
      exact S.
  Defined.

  (*  This does not hold, but hints at what we want to ask for
  Lemma foobar : functor_composite T (section_functor S) = functor_composite section_functor_pair (total_tensor T TT).
  Proof.
    apply functor_eq.
    - apply homset_property.
    - cbn.
      use total2_paths_f.
      + cbn.
        apply funextsec.
        intros [c c'].
        cbn.
        use total2_paths_f.
        * apply idpath.
        * cbn.
 *)


  (**
        For a strict monoidal functor, the square above should commute
        up to a displayed natural isomorphism in the D that is the identity in C
   *)

  Definition monoidal_tensor_section_data : UU
    := ∏ (c c' : C),
      iso_disp
        (identity_iso (T (c,,c')))
        (S (T (c,,c')))
        (TT _ ((S c,, S c') : (D ⊠⊠ D)(c,,c'))).

  (*
     Without the identity coercerion [displayed_tensor_to_disp_functor] above,
     we would need to write
     disp_functor_on_objects (TT : disp_functor _ _ _) ((S c,, S c') : (D ⊠⊠ D)(c,,c'))
     instead of
     TT _ ((S c,, S c') : (D ⊠⊠ D)(c,,c'))
   *)

  (** Naturality for [monoidal_tensor_section_data]

     S(T(c₁ c₁')) ---α(c₁ c₁')---> TT(Sc₁, Sc₁')
                |                  |
    S(T(f₁ f₂)  |                  | TT(Sf₁,Sf₂)
                v                  v
     S(T(c₂ c₂')) ---α(c₂ c₂')---> TT(Sc₂, c₂')

    Note that this equation is ill-typed:
    the down-then-horizontal lives over T(f₁,f₂) · id_iso,
    the horizontal-then-down lives over id_iso · T(f₁,f₂)
    We transport them both to live over T(f₁,f₂)
   *)

  Definition monoidal_tensor_section_natural (α : monoidal_tensor_section_data)
    : UU
    :=
    ∏ (c₁ c₁' c₂ c₂' : C) (f : c₁ --> c₂) (f' : c₁' --> c₂'),
      transportf
        (mor_disp _ _ )
        (id_right _ )
        (section_disp_on_morphisms S ((#T ( f ⊠' f')) %cat) ;; α _ _)
      =
        transportf
          (mor_disp _ _ )
          (id_left _ )
          (α _ _ ;; #TT (section_disp_on_morphisms S f ⊠⊠' (section_disp_on_morphisms S f'))).

  Definition monoidal_tensor_section : UU
    := ∑ (α : monoidal_tensor_section_data), monoidal_tensor_section_natural α.

  Coercion monoidal_tensor_section_data_from_monoidal_tensor_section (α : monoidal_tensor_section)
    : monoidal_tensor_section_data
    := pr1 α.

  Definition monoidal_tensor_ax
             (α : monoidal_tensor_section)
             (c₁ c₁' c₂ c₂' : C)
             (f : c₁ --> c₂)
             (f' : c₁' --> c₂')
    :
    transportf
        (mor_disp _ _ )
        (id_right _ )
        (section_disp_on_morphisms S ((#T ( f ⊠' f')) %cat) ;; pr1 α _ _)
      =
        transportf
          (mor_disp _ _ )
          (id_left _ )
          (pr1 α _ _ ;; #TT (section_disp_on_morphisms S f ⊠⊠' (section_disp_on_morphisms S f')))
    := pr2 α _ _ _ _ f f'.

  Definition monoidal_tensor_ax'
             (α : monoidal_tensor_section)
             (c₁ c₁' c₂ c₂' : C)
             (f : c₁ --> c₂)
             (f' : c₁' --> c₂')
    :
        (section_disp_on_morphisms S ((#T ( f ⊠' f')) %cat) ;; pr1 α _ _)
      =
        transportb
          (mor_disp _ _ )
          (id_right _ )
          (
            transportf
              (mor_disp _ _ )
              (id_left _ )
              (pr1 α _ _ ;; #TT (section_disp_on_morphisms S f ⊠⊠' (section_disp_on_morphisms S f')))).
  Proof.
    apply transportf_transpose_right.
    etrans. 2 : { apply monoidal_tensor_ax. }
    apply transportf_paths.
    apply C.
  Qed.



  (* Sanity check looks ok, but is cumbersome to prove *)

  Local Definition sanity_check (α : monoidal_tensor_section)
    : nat_iso
        (functor_composite T (section_functor S))
        (functor_composite section_functor_pair (total_tensor T TT)).
  Proof.
    use make_nat_iso.
    - use make_nat_trans.
      + intro a.
        cbn.
        use tpair.
        * exact (identity_iso _ ).
        * cbn. apply α.
      + cbn.
        intros [a a'] [b b'] [f f'].
        cbn in *.
        use total2_paths_f.
        * (* we can prove this in an ugly way, since in the next goal
             we are transporting along equality between elements of
             a set anyway
             For getting a clean display, it would even be good to
             prove this equality separately and make it `Qed.`.
           *)
          (*cbn.
          etrans.
          apply id_right.
          etrans.
          2 : { eapply pathsinv0. apply id_left. }
          apply maponpaths.

          repeat rewrite id_left.
          repeat rewrite id_right.
          apply idpath.
           *)
          admit.
        * cbn.
          etrans.
          apply maponpaths.
          apply monoidal_tensor_ax'.
          etrans. { apply transport_f_f. }
          etrans. { apply transport_f_f. }
          apply pathsinv0.
          set (X := @disp_functor_comp _ _ _ _ _ TT).
          etrans. {
                  apply maponpaths.
                  set (X':= @X (a,,a') (b,,b') (b,,b') (S a,, S a') (S b,,S b') (S b,,S b')).
                  set (X'' := @X'
                                ((id _ · f) ⊠' (id _ · f')) (identity b ⊠' id b')).
                  set (X3 := X'' ((id_disp (S a) ;; section_disp_on_morphisms S f) ⊠⊠'(id_disp (S a') ;; section_disp_on_morphisms S f') )).
                  set (X4 := X3 (id_disp (S b) ⊠⊠' (id_disp (S b')))).
                  apply X4.
                }
                cbn.
          etrans.
          { apply mor_disp_transportf_prewhisker. }
          etrans.
          { apply maponpaths.
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              set (X' := @disp_functor_id _ _ _ _ _ TT).
              apply (X' (b,,b')).
            }
            apply mor_disp_transportf_prewhisker.
          }
          etrans.
          { apply maponpaths.
            apply mor_disp_transportf_prewhisker. }
          etrans.
          {
            apply maponpaths.
            apply maponpaths.
            apply maponpaths.
            apply id_right_disp.
          }
          etrans.
          {
            apply maponpaths.
            apply maponpaths.
            apply mor_disp_transportf_prewhisker.
          }
          etrans.
          { apply transport_f_f. }
          etrans.
          { apply transport_f_f. }
          etrans.
          {
            apply maponpaths.
            apply maponpaths.
            set (X':= @X (a,,a') (a,,a') (b,,b') (S a,, S a') (S a,,S a') (S b,,S b')).
            set (X'' := @X'
                          (identity a ⊠' id a') (f ⊠' f') ).
            set (X3 := X'' (id_disp _ ⊠⊠' (id_disp _ ))
                           (section_disp_on_morphisms S f ⊠⊠' section_disp_on_morphisms S f')
                ).
            apply X3.
          }
          etrans.
          { apply maponpaths.
            apply mor_disp_transportf_prewhisker.
          }
          etrans.
          { apply transport_f_f. }
          etrans.

          { apply maponpaths.
            apply maponpaths.
            apply maponpaths_2.
            set (X' := @disp_functor_id _ _ _ _ _ TT).
            apply (X' (a,,a')).
          }
          etrans.
          { apply maponpaths.
            apply assoc_disp.
          }
          etrans.
          { apply transport_f_f.
          }
          etrans.
          { apply maponpaths.
            apply maponpaths_2.
            apply mor_disp_transportf_prewhisker.
          }
          etrans.
          { apply maponpaths.
            apply mor_disp_transportf_postwhisker.
          }
          etrans.
          { apply transport_f_f.
          }
          etrans.
          { apply maponpaths.
            apply maponpaths_2.
            apply id_right_disp.
          }
          etrans.
          { apply maponpaths.
            apply  mor_disp_transportf_postwhisker.
          }
          etrans.
          { apply transport_f_f. }
          apply two_arg_paths.
          -- apply C.
          -- apply idpath.
    - intros a b f. cbn.
      admit.
  Abort.

End section_tensor.


Section FixDispTensor.

  Context {C : category}
          (tensor : C ⊠ C ⟶ C)
          {D : disp_cat C}
          (disp_tensor : displayed_tensor tensor D).

  Let al : functor _ _ := assoc_left tensor.
  Let ar : functor _ _ := assoc_right tensor.

  Definition disp_assoc_left : @disp_functor ((C ⊠ C) ⊠ C) C al  ((D ⊠⊠ D) ⊠⊠ D) D .
  Proof.
    use disp_functor_composite.
    - use (disp_binprod D D).
    - use disp_pair_functor.
      + use disp_tensor.
      + use disp_functor_identity.
    - use disp_tensor.
  Defined.



  (* TODO
  Definition disp_assoc_right : @disp_functor (C ⊠ (C ⊠ C)) C ar  (D ⊠⊠ (D ⊠⊠ D)) D .
  Proof.
    use disp_functor_composite.
    - use (disp_binprod D D).
    - use disp_pair_functor.
      + use disp_tensor.
      + use disp_functor_identity.
    - use disp_tensor.
  Defined.
*)


End FixDispTensor.
