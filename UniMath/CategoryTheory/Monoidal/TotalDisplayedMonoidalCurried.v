(* In this file we show:
   1. If a displayed category over a monoidal category has the structure of a displayed monoidal category,
      then has the total category the structure of a monoidal category.
   2. The projection from the total category (equipped with this monoidal structure) to the base (monoidal) category
      is a strict monoidal functor.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesCurried.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalCurried.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsCurried.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section MonoidalTotalCategory.

  Context (C : category) (T : tensor_data C) (I : C) (α : associator_data T) (lu : leftunitor_data T I) (ru : rightunitor_data T I) (tid : tensorfunctor_id T) (tcomp : tensorfunctor_comp T) (αnat : associator_naturality α) (αiso : associator_is_natiso α) (lunat : leftunitor_naturality lu) (luiso : leftunitor_is_natiso lu) (runat : rightunitor_naturality ru) (ruiso : rightunitor_is_natiso ru) (tri : triangle_identity lu ru α) (pen : pentagon_identity α)
          (D : disp_cat C) (dtd : displayedtensor_data C D T) (i : D I) (dα : displayedassociator_data C D T α dtd) (dlu : displayedleftunitor_data C D T I lu dtd i) (dru : displayedrightunitor_data C D T I ru dtd i) (dtid : displayedtensor_id C D T tid dtd) (dtcomp : displayedtensor_comp C D T tcomp dtd) (dαnat : displayedassociator_naturality C D T α αnat dα ) (dαiso : displayedassociator_is_nat_iso C D T α αiso dα ) (dlunat : displayedleftunitor_naturality C D T I lu lunat dlu ) (dluiso : displayedleftunitor_is_nat_iso C D T I lu luiso dlu) (drunat : displayedrightunitor_naturality C D T I ru runat dru ) (druiso : displayedrightunitor_is_nat_iso C D T I ru ruiso dru) (dtri : displayedtriangle_identity C D T I α lu ru tri dlu dru dα) (dpen : displayedpentagon_identity C D T α pen dα).

  Notation ToD := (total_category D).
  Notation "x ⊗_{ T } y" := (tensoronobjects_from_tensordata T x y) (at level 31).
  Notation "f ⊗^{ T } g" := (tensoronmorphisms_from_tensordata T  _ _ _ _ f g) (at level 31).
  Notation "a ⊗_{{ dtd }} b" := (displayedtensoronobjects_from_displayedtensordata _ _ _ dtd _ _ a b) (at level 31).
  Notation "f' ⊗^{{ dtd }} g'" := (displayedtensoronmorphisms_from_displayedtensordata dtd _ _ _ _ _ _ _ _ _ _ f' g'  ) (at level 31).

  (** DATA **)
  Definition totalcategory_tensordata : tensor_data ToD.
  Proof.
    use tpair.
    + intros xa yb.
      exact ((pr1 xa) ⊗_{T} (pr1 yb) ,, (pr2 xa) ⊗_{{dtd}} (pr2 yb)).
    +  intros xa yb xa' yb' f g.
       split with (pr1 f ⊗^{T} pr1 g).
       apply (pr2 dtd).
       - exact (pr2 f).
       - exact (pr2 g).
  Defined.
  Notation TtD := totalcategory_tensordata.

  Definition totalcategory_associatordata : associator_data TtD.
  Proof.
    intros x y z.
    use tpair.
    + exact (α (pr1 x) (pr1 y) (pr1 z)).
    + exact (dα (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)).
  Defined.
  Notation TαD := totalcategory_associatordata.

  Definition totalcategory_unitdata : ToD := (I,,i).
  Notation TuD := totalcategory_unitdata.

  Definition totalcategory_leftunitordata : leftunitor_data TtD TuD.
  Proof.
    intro x.
    use tpair.
    + apply lu.
    + exact (dlu (pr1 x) (pr2 x)).
  Defined.
  Notation TluD := totalcategory_leftunitordata.

  Definition totalcategory_rightunitordata : rightunitor_data TtD TuD.
  Proof.
    intro x.
    use tpair.
    + apply ru.
    + exact (dru (pr1 x) (pr2 x)).
  Defined.
  Notation TruD := totalcategory_rightunitordata.

  Definition totalcategory_monoidalcatdata : (monoidalcategory_data ToD) := (TtD,,TuD,,TluD,,TruD,,TαD).

  (** PROPERTIES **)
  Lemma totalcategory_tensorfunctorid : tensorfunctor_id TtD.
  Proof.
    intros x y.
    use total2_paths_b.
    + apply tid.
    + apply (dtid (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma totalcategory_tensorfunctorcomp : tensorfunctor_comp TtD.
  Proof.
    intros x y x' y' x'' y'' f f' g g'.
    use total2_paths_b.
    + use tcomp.
    + use (((dtcomp (pr1 x) (pr1 y) (pr1 x') (pr1 y') (pr1 x'') (pr1 y'')
                         (pr2 x) (pr2 y) (pr2 x') (pr2 y') (pr2 x'') (pr2 y'')
                         (pr1 f) (pr1 g) (pr1 f') (pr1 g')
                         (pr2 f) (pr2 g) (pr2 f') (pr2 g')))).
  Qed.

  Lemma totalcategory_associatornaturality : associator_naturality TαD.
  Proof.
    intros x x' y y' z z' f g h.
    use total2_paths_b.
    - exact (αnat (pr1 x) (pr1 x') (pr1 y) (pr1 y') (pr1 z) (pr1 z') (pr1 f) (pr1 g) (pr1 h)).
    - exact (dαnat (pr1 x) (pr1 x') (pr1 y) (pr1 y') (pr1 z) (pr1 z')
                        (pr2 x) (pr2 x') (pr2 y) (pr2 y') (pr2 z) (pr2 z')
                        (pr1 f) (pr1 g) (pr1 h) (pr2 f) (pr2 g) (pr2 h)).
  Qed.

  Lemma totalcategory_associatorisnatiso : associator_is_natiso TαD.
  Proof.
    intros x y z.
    use tpair.
    + use tpair.
    - exact (pr1 (αiso (pr1 x) (pr1 y) (pr1 z))).
    - cbn.
      set (pf :=  (((pr2 (pr1 (pr2(pr1 C)))) _ _) (pr1 (αiso (pr1 x) (pr1 y) (pr1 z))))).
      (* pf : Isos.inv_from_iso (Isos.z_iso_to_iso (α (pr1 x) (pr1 y) (pr1 z),, αiso (pr1 x) (pr1 y) (pr1 z))) = pr1 (αiso (pr1 x) (pr1 y) (pr1 z))) *)
      admit.
      (*
      exact (transportf (*(mor_disp (pr2 x ⊗_{{ dtd}} (pr2 y ⊗_{{ dtd}} pr2 z))
          ((pr2 x ⊗_{{ dtd}} pr2 y) ⊗_{{ dtd}} pr2 z))*) _ pf (pr1 (dαiso (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)))).
*)
      + use tpair.
        - use total2_paths_b.
          -- exact (pr1 (pr2 (αiso (pr1 x) (pr1 y) (pr1 z)))).
          -- admit. (* etrans. { apply mor_disp_transportf_prewhisker. }
             apply transportb_transpose_right.
             etrans.
             { apply transport_f_f. }

             etrans. {
              apply maponpaths.
              apply (pr2 (pr2 (dαiso (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)))).
             }
             etrans. { apply transport_f_f. }
             apply transportf_set.
             apply homset_property. *)
        - use total2_paths_b.
          -- exact (pr2 (pr2 (αiso (pr1 x) (pr1 y) (pr1 z)))).
          -- admit.
             (* etrans. { apply mor_disp_transportf_postwhisker. }
             apply transportb_transpose_right.
             etrans.
             { apply transport_f_f. }

             etrans. {
              apply maponpaths.
              apply (pr1 (pr2 (dαiso (pr1 x) (pr1 y) (pr1 z) (pr2 x) (pr2 y) (pr2 z)))).
            }
            etrans. { apply transport_f_f. }
            apply transportf_set.
             apply homset_property.
  Qed.
       *)
      Admitted.


  Lemma totalcategory_leftunitornaturality : leftunitor_naturality TluD.
  Proof.
    intros x y f.
    use total2_paths_b.
    + exact (lunat (pr1 x) (pr1 y) (pr1 f)).
    + exact (dlunat (pr1 x) (pr1 y) (pr2 x) (pr2 y) (pr1 f) (pr2 f)).
  Qed.

  Lemma totalcategory_leftunitorisnatiso : leftunitor_is_natiso TluD.
  Proof.
    intros x.
    use tpair.
    + use tpair.
    - exact (pr1 (luiso (pr1 x))).
    - set (pf (*: Isos.inv_from_iso (Isos.z_iso_to_iso (lu (pr1 x),, luiso (pr1 x))) = pr1 (luiso (pr1 x))*)
           := (((pr2 (pr1 (pr2(pr1 C)))) _ _) (pr1 (luiso (pr1 x))))
          ).
      admit. (*
      exact (transportf _ pf (pr1 (dluiso (pr1 x) (pr2 x)))). *)
      + use tpair.
        - use total2_paths_b.
          -- exact (pr1 (pr2 (luiso (pr1 x)))).
          -- admit. (* etrans.
             { apply mor_disp_transportf_prewhisker. }
             apply transportb_transpose_right.
             etrans.
             { apply transport_f_f. }
             etrans. {
              apply maponpaths.
              apply (pr2 (pr2 (dluiso (pr1 x) (pr2 x)))).
             }
             etrans. { apply transport_f_f. }
             apply transportf_set.
             apply homset_property. *)
        - use total2_paths_b.
          -- exact (pr2 (pr2 (luiso (pr1 x)))).
          -- admit. (* etrans.
             { apply mor_disp_transportf_postwhisker. }
             apply transportb_transpose_right.
             etrans.
             { apply transport_f_f. }
             etrans. {
              apply maponpaths.
              apply (pr1 (pr2 (dluiso (pr1 x) (pr2 x)))).
             }
             etrans. { apply transport_f_f. }
             apply transportf_set.
             apply homset_property.
  Qed. *)
             Admitted.

  Lemma totalcategory_rightunitornaturality : rightunitor_naturality TruD.
  Proof.
    intros x y f.
    use total2_paths_b.
    + exact (runat (pr1 x) (pr1 y) (pr1 f)).
    + exact (drunat (pr1 x) (pr1 y) (pr2 x) (pr2 y) (pr1 f) (pr2 f)).
  Qed.

  Lemma totalcategory_rightunitorisnatiso : rightunitor_is_natiso TruD.
  Proof.
    intros x.
    use tpair.
    + use tpair.
    - exact (pr1 (ruiso (pr1 x))).
    - set (pf (*: Isos.inv_from_iso (Isos.z_iso_to_iso (lu (pr1 x),, luiso (pr1 x))) = pr1 (luiso (pr1 x))*)
           := (((pr2 (pr1 (pr2(pr1 C)))) _ _) (pr1 (ruiso (pr1 x))))
          ).
      admit.
      (* exact (transportf _ pf (pr1 (druiso (pr1 x) (pr2 x)))). *)
      + use tpair.
        - use total2_paths_b.
          -- exact (pr1 (pr2 (ruiso (pr1 x)))).
          -- admit. (* etrans.
             { apply mor_disp_transportf_prewhisker. }
             apply transportb_transpose_right.
             etrans.
             { apply transport_f_f. }

             etrans. {
              apply maponpaths.
              apply (pr2 (pr2 (druiso (pr1 x) (pr2 x)))).
            }
            etrans. { apply transport_f_f. }

             apply transportf_set.
             apply homset_property.

*)
        - use total2_paths_b.
          -- exact (pr2 (pr2 (ruiso (pr1 x)))).
          -- admit. (* etrans.
             { apply mor_disp_transportf_postwhisker. }
             apply transportb_transpose_right.
             etrans.
             { apply transport_f_f. }

             etrans. {
              apply maponpaths.
              apply (pr1 (pr2 (druiso (pr1 x) (pr2 x)))).
            }
            etrans. { apply transport_f_f. }

             apply transportf_set.
             apply homset_property.
  Qed. *)
             Admitted.

  Lemma totalcategory_triangleidentity : triangle_identity TluD TruD TαD.
  Proof.
    intros x y.
    use total2_paths_b.
    + exact (tri (pr1 x) (pr1 y)).
    + exact (dtri (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
  Qed.

  Lemma totalcategory_pentagonidentity : pentagon_identity TαD.
  Proof.
    intros w x y z.
    use total2_paths_b.
    + exact (pen (pr1 w) (pr1 x) (pr1 y) (pr1 z)).
    + exact (dpen (pr1 w) (pr1 x) (pr1 y) (pr1 z) (pr2 w) (pr2 x) (pr2 y) (pr2 z)).
  Qed.

  Definition totalcategory_monoidallaws : monoidal_laws totalcategory_monoidalcatdata :=
    (totalcategory_tensorfunctorid,, totalcategory_tensorfunctorcomp,,
                                     totalcategory_associatornaturality,, totalcategory_associatorisnatiso,,
                                     totalcategory_leftunitornaturality,, totalcategory_leftunitorisnatiso,,
                                     totalcategory_rightunitornaturality,, totalcategory_rightunitorisnatiso,,
                                     totalcategory_triangleidentity,, totalcategory_pentagonidentity).

  Definition totalcategory_monoidalcat : monoidalcategory ToD := (totalcategory_monoidalcatdata,, totalcategory_monoidallaws).

  Notation π := (pr1_category D).
  Definition MC : monoidalcategory_data C := (T,,I,,lu,,ru,,α).

  Definition projection_tensorpreservingdata : tensor_preserving_data ToD C totalcategory_monoidalcatdata MC π := λ x y, identity (π x ⊗_{ MC} π y).
  Definition projection_unitpreservingdata : unit_preserving_data ToD C totalcategory_monoidalcatdata MC π := identity I.

  Definition projection_monoidalfunctordata : monoidalfunctor_data ToD C totalcategory_monoidalcatdata MC π :=
  (projection_tensorpreservingdata,,projection_unitpreservingdata).

  Lemma projection_tensornaturality : tensor_preserving_data_is_natural ToD C totalcategory_monoidalcatdata MC π projection_tensorpreservingdata.
  Proof.
    intros xx yy zz ww ff' gg'.
    exact ((pr1 (pr1 (pr2 (pr1 C))) _ _ (pr1 ff' ⊗^{T} pr1 gg')) @ (pathsinv0 (pr2 (pr1 (pr2 (pr1 C))) _ _ (pr1 ff' ⊗^{T} pr1 gg')))).
  Qed.

  Lemma projection_preservesassociativity : preserves_associativity ToD C totalcategory_monoidalcatdata MC π projection_tensorpreservingdata.
  Proof.
    intros xx yy zz.
    rewrite (pr1 (pr1 (pr2 (pr1 C)))).
    rewrite (pr2 (pr1 (pr2 (pr1 C)))).
    rewrite tid.
    rewrite tid.
    rewrite (pr1 (pr1 (pr2 (pr1 C)))).
    rewrite (pr2 (pr1 (pr2 (pr1 C)))).
    apply idpath.
  Qed.

  Lemma projection_preservesleftunitality : preserves_leftunitality ToD C totalcategory_monoidalcatdata MC π projection_tensorpreservingdata projection_unitpreservingdata.
  Proof.
    intro xx.
    rewrite tid.
    rewrite (pr1 (pr1 (pr2 (pr1 C)))).
    rewrite (pr1 (pr1 (pr2 (pr1 C)))).
    apply idpath.
  Qed.

  Lemma projection_preservesrightunitality : preserves_rightunitality ToD C totalcategory_monoidalcatdata MC π projection_tensorpreservingdata projection_unitpreservingdata.
  Proof.
    intro xx.
    rewrite tid.
    rewrite (pr1 (pr1 (pr2 (pr1 C)))).
    rewrite (pr1 (pr1 (pr2 (pr1 C)))).
    apply idpath.
  Qed.

  Definition projection_monoidallaws : monoidalfunctor_laws ToD C totalcategory_monoidalcatdata MC π projection_monoidalfunctordata
    := (projection_tensornaturality,,projection_preservesassociativity,,projection_preservesleftunitality,,projection_preservesrightunitality).

  Definition projection_monoidalfunctor : monoidalfunctor ToD C totalcategory_monoidalcatdata MC π
    := (projection_monoidalfunctordata,,projection_monoidallaws).

  Lemma projection_strictlytensorpreserving : is_strictlytensorpreserving ToD C totalcategory_monoidalcatdata MC π projection_tensorpreservingdata.
  Proof.
    intros xx yy.
    use tpair.
    + apply idpath.
    + apply idpath.
  Qed.

  Lemma projection_strictlyunitpreserving : is_strictlyunitpreserving ToD C totalcategory_monoidalcatdata MC π projection_unitpreservingdata.
  Proof.
    use tpair.
    + apply idpath.
    + apply idpath.
  Qed.

End MonoidalTotalCategory.
