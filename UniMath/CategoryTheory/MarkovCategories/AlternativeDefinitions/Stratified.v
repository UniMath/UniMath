(*********************************************

This is an equivalent reorganization of the data of Markov categories.
The main purpose is to have an easier dependency structure of the data which
is helpful for the proofs in `EquivalenceQuasicartesianMarkov.v`.

The data is organized similar to the way one would define a GAT of Markov categories:
- Signature: tensor on objects ⊗, unit I
- Structure: 
  * tensor on morphisms
  * all coherence maps
  * symmetry
  * Markov structure 
- Laws: all equations (this is a proposition)

*********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.

Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.

Import MonoidalNotations.

Section Signature.

  Definition mon_sig (C : category) := (C -> C -> C) × C.
  Definition mon_sig_cat := ∑ C : category, mon_sig C.
  Definition mon_sig_cat_to_cat : mon_sig_cat -> category := pr1.

  Coercion mon_sig_cat_to_cat : mon_sig_cat >-> category.

  Definition I {C : mon_sig_cat} : C := pr22 C.
  Definition tensor {C : mon_sig_cat} (x y : C) : C := pr12 C x y.

End Signature.

Local Notation "x ⊗ y" := (tensor x y).

Section Structure.

  Definition markov_struct (C : mon_sig_cat) : UU.
  Proof.
    refine (
        (* Left whisker *)
      (∏ (a : C) (b1 b2 : C), C ⟦ b1, b2 ⟧ → C ⟦ a ⊗ b1, a ⊗ b2 ⟧)
      × (* Right whisker *)
      (∏ (b : C) (a1 a2 : C), C ⟦ a1, a2 ⟧ → C ⟦ a1 ⊗ b, a2 ⊗ b ⟧)
      × (* Left unitor *)
      (∏ x : C, C ⟦ I ⊗ x, x ⟧)
      × (* Left inv unitor *)
      (∏ x : C, C ⟦ x, I ⊗ x ⟧)
      × (* Right unitor *)
      (∏ x : C, C ⟦ x ⊗ I, x ⟧)
      × (* Right inv unitor *)
      (∏ x : C, C ⟦ x, x ⊗ I ⟧)
      × (* Associator *)
      (∏ x y z : C, C ⟦ (x ⊗ y) ⊗ z, x ⊗ (y ⊗ z) ⟧)
      × (* Inv associator *)
      (∏ x y z : C, C ⟦ x ⊗ (y ⊗ z), (x ⊗ y) ⊗ z ⟧)
      × (* Symmetry *)
      (∏ x y : C, C ⟦ x ⊗ y, y ⊗ x ⟧)
      × (* Delete *)
      (∏ x : C, C ⟦ x, I ⟧)
      × (* Copy *)
      (∏ x : C, C ⟦ x, x ⊗ x ⟧)
    ).
  Defined.

  Definition markov_struct_cat := ∑ C : mon_sig_cat, markov_struct C.

  Definition markov_struct_cat_to_mon_sig_cat : markov_struct_cat -> mon_sig_cat := pr1.
  Coercion markov_struct_cat_to_mon_sig_cat : markov_struct_cat >-> mon_sig_cat.

  Section MarkovStructAccessors.
    Context {C : markov_struct_cat}.

    Definition whisker_l (x : C) {y z : C} (g : y --> z) 
      : (x ⊗ y) --> (x ⊗ z) := (pr12 C) _ _ _ g.
    Definition whisker_r (z : C) {x y : C} (f : x --> y) 
      : (x ⊗ z) --> (y ⊗ z) := (pr122 C) _ _ _ f.

    Definition tensor_mor {x1 x2 y1 y2 : C} (f : x1 --> y1) (g : x2 --> y2) : (x1 ⊗ x2) --> (y1 ⊗ y2) 
      := (whisker_r _ f) · (whisker_l _ g).

    Definition leftunitor (x : C) : C ⟦ I ⊗ x, x ⟧ := pr1 (pr222 C) x.
    Definition leftunitorinv (x : C) : C ⟦ x, I ⊗ x ⟧ := pr12 (pr222 C) x.

    Definition rightunitor (x : C) : C ⟦ x ⊗ I, x ⟧ := pr122 (pr222 C) x.
    Definition rightunitorinv (x : C) : C ⟦ x, x ⊗ I ⟧ := pr1 (pr222 (pr222 C)) x.

    Definition associator (x y z : C) : C ⟦ (x ⊗ y) ⊗ z, x ⊗ (y ⊗ z) ⟧ := pr12 (pr222 (pr222 C)) x y z.
    Definition associatorinv (x y z : C) : C ⟦ x ⊗ (y ⊗ z), (x ⊗ y) ⊗ z ⟧ 
      := pr122 (pr222 (pr222 C)) x y z.

    Definition swap (x y : C) : C ⟦ x ⊗ y, y ⊗ x ⟧ := pr1 (pr222 (pr222 (pr222 C))) x y.

    Definition delete (x : C) : C ⟦ x, I ⟧ := pr12 (pr222 (pr222 (pr222 C))) x.
    Definition copy (x : C) : C ⟦ x, x ⊗ x ⟧ := pr22 (pr222 (pr222 (pr222 C))) x.
  End MarkovStructAccessors.

End Structure.

Local Notation "x ⊗ y" := (tensor x y).
Local Notation "f #⊗ g" := (tensor_mor f g).

Section Laws.
  Context (C : markov_struct_cat).

  Definition markov_tensor_data : tensor_data C.
  Proof.
    use make_bifunctor_data.
    - exact tensor.
    - exact (@whisker_l C).
    - exact (@whisker_r C).
  Defined.

  Definition markov_monoidal_data : monoidal_data C.
  Proof.
    use make_monoidal_data.
    - exact markov_tensor_data.
    - exact I.
    - exact leftunitor.
    - exact leftunitorinv.
    - exact rightunitor.
    - exact rightunitorinv.
    - exact (@associator C).
    - exact (@associatorinv C).
  Defined.  

  Definition symmetry_inv : UU := ∏ x y : C, swap x y · swap y x = identity _.
  Definition symmetry_nat : UU := ∏ (x1 x2 y1 y2 : C)
      (f : C ⟦ x1, x2 ⟧)
      (g : C ⟦ y1, y2 ⟧),
      f #⊗ g · swap x2 y2 =
      swap x1 y1 · g #⊗ f.
  Definition symmetry_hexagon := ∏ x y z : C,
      associator x y z · swap x (tensor y z)
      · associator y z x =
      (swap x y) #⊗ (identity z) · associator y
      x z
      · (identity y) #⊗ (swap x z).

  Definition symmetry_laws : UU := 
    symmetry_inv
    ×
    symmetry_nat
    ×
    symmetry_hexagon.

  Definition semicartesianness : UU :=
    (∏ x : C, ∏ f : (x --> I), f = delete x).

  Definition copy_assoc : UU := ∏ (x : C),
        copy x · (identity _ #⊗ copy x)
      = copy x · (copy x #⊗ identity _) · associator _ _ _.

  Definition copy_del_r : UU := ∏ (x : C),
        copy x · (identity _ #⊗ delete x) · rightunitor _
      = identity _.

  Definition copy_del_l : UU := ∏ (x : C),
        copy x · (delete x #⊗ identity _) · leftunitor _
      = identity _.

  Definition copy_comm : UU := ∏ (x : C),
        copy x · swap _ _
      = copy x.

  Definition inner_swap (x y z w : C)
    : C ⟦(x ⊗ y) ⊗ (z ⊗ w), (x ⊗ z) ⊗ (y ⊗ w)⟧.
  Proof.
    refine (associator _ _ _ · _).
    refine (_ · associatorinv _ _ _).
    refine (whisker_l _ _).
    refine (associatorinv _ _ _ · _).
    refine (_ · associator _ _ _).
    exact (whisker_r _ (swap y z)).
  Defined.

  Definition copy_tensor : UU := ∏ (x y : C),
        (copy x #⊗ copy y) · inner_swap _ _ _ _
      = copy (x ⊗ y).

  Definition copydelete_laws : UU := 
    copy_assoc
    ×
    copy_del_r
    ×
    copy_del_l
    ×
    copy_comm
    ×
    copy_tensor.

  Definition markov_laws : UU := 
    monoidal_laws markov_monoidal_data
    × 
    symmetry_laws
    ×
    semicartesianness
    ×
    copydelete_laws.

  Proposition isaprop_markov_laws : isaprop markov_laws.
  Proof.
    (repeat apply isapropdirprod)
    ; repeat (apply impred_isaprop; intros)
    ; try (apply homset_property || apply Isos.isaprop_is_inverse_in_precat).
  Qed.
  
End Laws.

Definition markov_laws_cat := ∑ C : markov_struct_cat, markov_laws C.
Definition markov_laws_cat_to_markov_struct_cat : markov_laws_cat -> markov_struct_cat := pr1.
Coercion markov_laws_cat_to_markov_struct_cat : markov_laws_cat >-> markov_struct_cat.

Section MarkovCategoryFromCat.
  Context (C : markov_laws_cat).

  Definition markov_monoidal_laws : monoidal_laws (markov_monoidal_data C) := pr12 C.
  Definition markov_monoidal : monoidal C := (markov_monoidal_data C ,, markov_monoidal_laws).
  Definition markov_monoidal_cat : monoidal_cat := ((C :> category),, markov_monoidal).

  (* Symmetry *)

  Definition markov_swap_laws : sym_mon_cat_laws_tensored markov_monoidal_cat swap.
  Proof.
    pose(symlaws := pr122 C). 
    repeat split.
    - exact (pr1 symlaws).
    - exact (pr12 symlaws).
    - exact (pr22 symlaws).
  Defined.

  Definition markov_symmetric : symmetric markov_monoidal.
  Proof.
    use (make_symmetric markov_monoidal_cat).
    - exact swap.
    - exact markov_swap_laws.
  Defined.
  
  Definition markov_sym_monoidal_cat : sym_monoidal_cat := (markov_monoidal_cat ,, markov_symmetric).

  (* Markov *)

  Definition markov_category_data : markov_category_data.
  Proof.
    pose (semicart := pr1 (pr222 C)).
    refine (markov_sym_monoidal_cat ,, _ ,, _).
    - intros x. refine (delete x ,, _). intros f. exact (semicart x f).
    - exact copy.
  Defined.

  Definition markov_category_laws : markov_category_laws markov_category_data.
  Proof.
    pose (cd := pr2 (pr222 C)).
    repeat split.
    - exact (pr1 cd).
    - exact (pr12 cd).
    - exact (pr122 cd).
    - exact (pr1 (pr222 cd)).
    - exact (pr2 (pr222 cd)).
  Defined.  

  Definition markov_category_from_cat : markov_category 
    := (markov_category_data ,, markov_category_laws).

End MarkovCategoryFromCat.

Section CatFromMarkovCategory.
  Context (C : markov_category).

  Local Open Scope markov.

  Definition sig : mon_sig C := (monoidal_cat_tensor_pt ,, I_{C}).
  Definition cat : mon_sig_cat := ((C :> category),, sig).

  Definition struct : markov_struct cat.
  Proof.
    repeat split.
    - apply leftwhiskering_on_morphisms.
    - apply rightwhiskering_on_morphisms.
    - exact mon_lunitor.
    - exact mon_linvunitor.
    - exact mon_runitor.
    - exact mon_rinvunitor.
    - exact mon_lassociator.
    - exact mon_rassociator.
    - apply sym_mon_braiding.
    - apply del.
    - apply MarkovCategory.copy.
  Defined.

  Definition struct_cat : markov_struct_cat := (cat ,, struct).
  
  Definition laws : markov_laws struct_cat.
  Proof.
    pose(moncat := pr111 C).
    refine (_ ,, _ ,, _ ,, _).
    - exact (pr22 moncat).
    - repeat split.
      * intros x y. apply sym_mon_braiding_inv.
      * intros x1 x2 y1 y2 f g. apply tensor_sym_mon_braiding.
      * intros x y z. apply sym_mon_hexagon_lassociator.
    - intros x f. apply markov_category_unit_eq.
    - repeat split.
      * intros x. apply MarkovCategory.copy_assoc'.
      * intros x. apply MarkovCategory.copy_del_r.
      * intros x. apply MarkovCategory.copy_del_l.
      * intros x. apply MarkovCategory.copy_comm.
      * intros x. apply MarkovCategory.copy_tensor.
  Defined.
  
  Definition laws_cat : markov_laws_cat := (struct_cat ,, laws).

End CatFromMarkovCategory.

Section Roundtrips.
  Definition markov_roundtrip (C : markov_category) 
    : markov_category_from_cat (laws_cat C) = C.
  Proof.
    
    destruct C as [[[Cmon [s slaws]] markov] l].
    use subtypePath. { intros cc. apply isaprop_markov_category_laws. }
    apply total2asstor_path. unfold total2asstor. cbn.
    apply maponpaths.
    apply total2asstor_path. unfold total2asstor. cbn.
    apply maponpaths.

    apply dirprod_paths.
    - apply isaprop_braiding_laws.
    - apply dirprod_paths.
      * apply funextsec2; intros x. cbn.
        apply isapropiscontr.
      * apply idpath.
  Defined.
  
  Definition markov_laws_cat_roundtrip (C : markov_laws_cat)
     : laws_cat (markov_category_from_cat C) = C.
  Proof.
    destruct C as [[sig struct] laws].
    use subtypePath. { intros cc. apply isaprop_markov_laws. }
    use total2_paths_f.
    - apply idpath.
    - etrans. { refine (idpath_transportf _ _). } 
      apply idpath.
  Defined.
End Roundtrips.

Definition markov_laws_weq :
  markov_category ≃ markov_laws_cat.
Proof.
  use weq_iso.
  - exact laws_cat.
  - exact markov_category_from_cat.
  - exact markov_roundtrip.
  - exact markov_laws_cat_roundtrip.
Defined.

Definition markov_laws_eq : 
  markov_category = markov_laws_cat.
Proof.
  exact (weqtopaths markov_laws_weq).
Defined.