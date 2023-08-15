Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

Section DisplayedCatIso.

  Context {C : category} (D : disp_cat C).

  Context
    (uo : ∏ c : C, iscontr (D c)).
  Context (uf : ∏ (c1 c2 : C) (f : C⟦c1,c2⟧),
              iscontr (pr1 (uo c1) -->[f] (pr1 (uo c2)))).

  Lemma uf_eq {c1 c2 : C} (f : C⟦c1,c2⟧)
    : ∏ (d1 : D c1) (d2 : D c2),
      (d1 -->[f] d2) ≃ (pr1 (uo c1) -->[f] pr1 (uo c2)).
  Proof.
    intros d1 d2.
    assert (p1 : d1 = pr1 (uo c1)).
    {
      apply uo.
    }

    assert (p2 : d2 = pr1 (uo c2)).
    {
      apply uo.
    }

    induction p1.
    induction p2.
    apply idweq.
  Defined.

  Lemma uf0 {c1 c2 : C} (f : C⟦c1,c2⟧)
    : ∏ (d1 : D c1) (d2 : D c2), iscontr (d1 -->[f] d2).
  Proof.
    intros d1 d2.
    use (iscontrweqb' (uf _ _ f)).
    apply uf_eq.
  Defined.

  Lemma weq_hom'
    {c1 : C} {c2 : C}
    (f : C ⟦ c1, c2 ⟧)
    : ∃! x : ∑ f0 : C ⟦ c1, c2 ⟧,
          pr1 (uo c1) -->[ f0] pr1 (uo c2),
          pr1 x = f.
  Proof.
    use tpair.
    - simple refine ((_ ,, _) ,, _).
      + exact f.
      + apply (pr1 (uf _ _ f)).
      + apply idpath.
    - intros [[g gg] p].
      use subtypePath.
      { intro ; apply homset_property. }
      use subtypePath.
      {
        intro.
        apply isapropifcontr.
        apply uf.
      }
      exact p.
  Qed.

  Lemma weq_hom
    {c1 : C} {c2 : C}
    (d1 : D c1)
    (d2 : D c2)
    (f : C ⟦ c1, c2 ⟧)
    : ∃! x : ∑ f0 : C ⟦ c1, c2 ⟧, d1 -->[ f0] d2, pr1 x = f.
  Proof.
    use tpair.
    - simple refine ((_ ,, _) ,, _).
      + exact f.
      + apply uf0.
      + apply idpath.
    - cbn.
      intros [[g gg] q].
      use subtypePath.
      { intro ; apply homset_property. }
      use subtypePath.
      {
        intro.
        apply isapropifcontr.
        apply uf0.
      }
      exact q.
  Qed.

  Lemma weq_ob (c : C)
    : ∃! x : ∑ x : C, D x, pr1 x = c.
  Proof.
    use tpair.
    - simple refine ((c ,, _) ,, _).
      + apply uo.
      + apply idpath.
    - intros [[c' d'] p].
      cbn in *.
      use total2_paths_f.
      + use subtypePath.
        { intro ; apply isapropifcontr, uo. }
        exact p.
      + simpl.
        etrans. {
          apply (transportf_total2_paths_f
                   (A := C) (B := λ x : C, D x) (λ x : C, x = c)).
        }
        induction p.
        apply idpath.
  Qed.

  Definition forgetful_is_iso
    : is_catiso (pr1_category D).
  Proof.
    split.
    - intros [c1 d1] [c2 d2] f.
      apply weq_hom.
    - intro c.
      apply weq_ob.
  Defined.

End DisplayedCatIso.

Section CatIsoToContractibleFibers.

  Context {C : category} {D : disp_cat C} (F : is_catiso (pr1_category D)).

  Let inv_i := inv_catiso (_ ,, F).

  Definition object_is_proj (x : C)
    : x = pr1 (inv_i x)
    := ! homotweqinvweq  (make_weq pr1 (pr2 F)) x.

  Definition object_as_proj_equal_fibers (x : C)
    : D x ≃ D (pr1 (inv_i x)).
  Proof.
    induction (object_is_proj x).
    apply idweq.
  Defined.

  Let W := invweq (catiso_ob_weq (_ ,, F)) : ob C ≃ ∑ x : C, D x.

  Lemma catiso_is_globally_prop' (x : C)
    : ∏ d1 d2 : D x, x ,, d1 = x ,, d2.
  Proof.
    intros d1 d2.
    set (g := isinclweq _ _ _ (pr2 (invweq W)) x).
    set (h := g ((x ,, d1) ,, idpath _) ((x ,, d2) ,, idpath _)).
    exact (base_paths _ _ (pr1 h)).
  Defined.

  Lemma catiso_is_globally_prop (x : C)
    : ∏ d1 d2 : D x, d1 = d2.
  Proof.
    intros d1 d2.
    set (h := total2_section_path x d2 (λ z, invweq (object_as_proj_equal_fibers z) (pr2 (inv_i z)))).
    refine (_ @ h (catiso_is_globally_prop' x _ d2)).

    set (h' := total2_section_path x d1 (λ z, invweq (object_as_proj_equal_fibers z) (pr2 (inv_i z)))).
    exact (! h' (catiso_is_globally_prop' x _ d1)).
  Defined.

  Definition catiso_is_globally_contr (x : C)
    : iscontr (D x).
  Proof.
    use (iscontrweqb' _ (object_as_proj_equal_fibers x)).
    use tpair.
    - exact (pr2 (inv_i x)).
    - intro ; apply catiso_is_globally_prop.
  Defined.

  (* Definition catiso_is_locally_contr'
    {x y : C} (f : C⟦x, y⟧)
    : iscontr (pr2 (inv_i x)
                 -->[Univalence.double_transport (object_is_proj x) (object_is_proj y) f]
                 pr2 (inv_i y)).
  Proof.
    set (ff := pr2 (#inv_i f)).
  Admitted.

  Definition catiso_is_locally_contr
    {x y : C} (f : C⟦x, y⟧)
    : iscontr (pr1 (catiso_is_globally_contr x) -->[f] pr1 (catiso_is_globally_contr y)).
  Proof.
    use (iscontrweqb' (catiso_is_locally_contr' f)).


  Defined. *)

End CatIsoToContractibleFibers.
