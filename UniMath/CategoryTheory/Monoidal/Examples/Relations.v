(********************************************************************************************

 The category of relations is symmetric monoidal closed

 In this file, we show that the category of relations is a symmetric monoidal closed
 category. The monoidal structure is defined by taking the product of sets. Note that this
 is not a cartesian monoidal structure, because products in the category of relations are
 disjoint unions.

 Contents
 1. The monoidal category of relations
 2. It is symmetric
 3. It is monoidal closed

 ********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Relations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

(**
 1. The monoidal category of relations
 *)
Definition tensor_data_REL
  : tensor_data REL.
Proof.
  use make_bifunctor_data.
  - exact (λ X₁ X₂, X₁ × X₂)%set.
  - exact (λ X Y₁ Y₂ R xy₁ xy₂, pr1 xy₁ = pr1 xy₂ ∧ R (pr2 xy₁) (pr2 xy₂))%logic.
  - exact (λ Y X₁ X₂ R xy₁ xy₂, pr2 xy₁ = pr2 xy₂ ∧ R (pr1 xy₁) (pr1 xy₂))%logic.
Defined.

Definition leftunitor_REL
  : leftunitor_data tensor_data_REL unitset
  := λ X x₁ x₂, (pr2 x₁ = x₂)%logic.

Definition leftunitorinv_REL
  : leftunitorinv_data tensor_data_REL unitset
  := λ X x₁ x₂, (pr2 x₂ = x₁)%logic.

Definition rightunitor_REL
  : rightunitor_data tensor_data_REL unitset
  := λ X x₁ x₂, (pr1 x₁ = x₂)%logic.

Definition rightunitorinv_REL
  : rightunitorinv_data tensor_data_REL unitset
  := λ X x₁ x₂, (pr1 x₂ = x₁)%logic.

Definition associator_REL
  : associator_data tensor_data_REL
  := λ X Y Z xyz₁ xyz₂,
     ((pr11 xyz₁ = pr1 xyz₂)
      ∧
      (pr21 xyz₁ = pr12 xyz₂)
      ∧
      (pr2 xyz₁ = pr22 xyz₂))%logic.

Definition associatorinv_REL
  : associatorinv_data tensor_data_REL
  := λ X Y Z xyz₁ xyz₂,
     ((pr11 xyz₂ = pr1 xyz₁)
      ∧
      (pr21 xyz₂ = pr12 xyz₁)
      ∧
      (pr2 xyz₂ = pr22 xyz₁))%logic.

Definition monoidal_data_REL
  : monoidal_data REL.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
  - exact tensor_data_REL.
  - exact unitset.
  - exact leftunitor_REL.
  - exact leftunitorinv_REL.
  - exact rightunitor_REL.
  - exact rightunitorinv_REL.
  - exact associator_REL.
  - exact associatorinv_REL.
Defined.

Proposition monoidal_laws_REL
  : monoidal_laws monoidal_data_REL.
Proof.
  split6.
  - repeat split.
    + intros X Y ; cbn.
      use funextsec ; intro xy₁.
      induction xy₁ as [ x₁ y₁ ].
      use funextsec ; intro xy₂.
      induction xy₂ as [ x₂ y₂ ] ; cbn.
      use hPropUnivalence.
      * intros p.
        use pathsdirprod.
        ** exact (pr1 p).
        ** exact (pr2 p).
      * intros p.
        split.
        ** exact (maponpaths dirprod_pr1 p).
        ** exact (maponpaths dirprod_pr2 p).
    + intros X Y ; cbn.
      use funextsec ; intro xy₁.
      induction xy₁ as [ x₁ y₁ ].
      use funextsec ; intro xy₂.
      induction xy₂ as [ x₂ y₂ ] ; cbn.
      use hPropUnivalence.
      * intros p.
        use pathsdirprod.
        ** exact (pr2 p).
        ** exact (pr1 p).
      * intros p.
        split.
        ** exact (maponpaths dirprod_pr2 p).
        ** exact (maponpaths dirprod_pr1 p).
    + intros X Y₁ Y₂ Y₃ g₁ g₂.
      use funextsec ; intro xy₁.
      induction xy₁ as [ x₁ y₁ ].
      use funextsec ; intro xy₂.
      induction xy₂ as [ x₂ y₂ ] ; cbn.
      use hPropUnivalence.
      * intros p.
        induction p as [ p q ].
        induction p.
        use (factor_through_squash _ _ q) ; [ apply propproperty | ] ; clear q.
        intros [ y q ].
        apply hinhpr.
        exact ((x₁ ,, y) ,, (idpath _ ,, pr1 q) ,, (idpath _ ,, pr2 q)).
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ y [ [ p₁ p₂ ] [ q₁ q₂ ]]] ; cbn in *.
        induction p₁, q₁.
        exact (idpath _ ,, hinhpr (pr2 y ,, p₂ ,, q₂)).
    + intros X Y₁ Y₂ Y₃ g₁ g₂.
      use funextsec ; intro xy₁.
      induction xy₁ as [ y₁ x₁ ].
      use funextsec ; intro xy₂.
      induction xy₂ as [ y₂ x₂ ] ; cbn.
      use hPropUnivalence.
      * intros p.
        induction p as [ p q ].
        induction p.
        use (factor_through_squash _ _ q) ; [ apply propproperty | ] ; clear q.
        intros [ y q ].
        exact (hinhpr ((y ,, x₁) ,, ((idpath _ ,, pr1 q) ,, (idpath _ ,, pr2 q)))).
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ y [ [ p₁ p₂ ] [ q₁ q₂ ]]] ; cbn in *.
        induction p₁, q₁.
        exact (idpath _ ,, hinhpr (_ ,, p₂ ,, q₂)).
    + intros X₁ X₂ Y₁ Y₂ R₁ R₂.
      use funextsec ; intro xy₁.
      induction xy₁ as [ y₁ x₁ ].
      use funextsec ; intro xy₂.
      induction xy₂ as [ y₂ x₂ ] ; cbn.
      use hPropUnivalence.
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ y [ [ p₁ p₂ ] [ q₁ q₂ ]]] ; cbn in *.
        induction p₁, q₁.
        exact (hinhpr ((_ ,, _) ,, ((idpath _ ,, q₂) ,, (idpath _ ,, p₂)))).
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ y [ [ p₁ p₂ ] [ q₁ q₂ ]]] ; cbn in *.
        induction p₁, q₁.
        exact (hinhpr ((_ ,, _) ,, ((idpath _ ,, q₂) ,, (idpath _ ,, p₂)))).
  - split.
    + intros X Y R.
      use funextsec ; intro x.
      induction x as [ [] x ].
      use funextsec ; intro y.
      use hPropUnivalence.
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ [ [] y' ] [ [ p₁ p₂ ] p₃ ]] ; cbn in *.
        induction p₃.
        exact (hinhpr (x ,, (idpath _ ,, p₂))).
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ a [ p q ]] ; cbn in *.
        induction p.
        exact (hinhpr ((tt ,, y) ,, ((idpath _ ,, q) ,, idpath _))).
    + intros X.
      split.
      * use funextsec ; intro x.
        induction x as [ [] x ].
        use funextsec ; intro x'.
        induction x' as [ [] x' ].
        use hPropUnivalence.
        ** use factor_through_squash ; [ apply propproperty | ].
           intros [ a [ p q ]] ; cbn in *.
           induction p, q.
           apply idpath.
        ** intro p ; cbn in *.
           refine (hinhpr (x' ,, _ ,, idpath _)).
           exact (maponpaths dirprod_pr2 p).
      * use funextsec ; intro x.
        use funextsec ; intro x'.
        use hPropUnivalence.
        ** use factor_through_squash ; [ apply propproperty | ].
           intros [ a [ p q ]] ; cbn in *.
           induction p, q.
           apply idpath.
        ** intro p ; cbn in *.
           induction p.
           exact (hinhpr ((tt ,, x) ,, idpath _ ,, idpath _)).
  - split.
    + intros X Y R.
      use funextsec ; intro x.
      induction x as [ x [] ].
      use funextsec ; intro y.
      use hPropUnivalence.
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ [ y' [] ] [ [ p₁ p₂ ] p₃ ]] ; cbn in *.
        induction p₃.
        exact (hinhpr (x ,, (idpath _ ,, p₂))).
      * use factor_through_squash ; [ apply propproperty | ].
        intros [ a [ p q ]] ; cbn in *.
        induction p.
        exact (hinhpr ((y ,, tt) ,, ((idpath _ ,, q) ,, idpath _))).
    + intros X.
      split.
      * use funextsec ; intro x.
        induction x as [ x [] ].
        use funextsec ; intro x'.
        induction x' as [ x' [] ].
        use hPropUnivalence.
        ** use factor_through_squash ; [ apply propproperty | ].
           intros [ a [ p q ]] ; cbn in *.
           induction p, q.
           apply idpath.
        ** intro p ; cbn in *.
           refine (hinhpr (x' ,, _ ,, idpath _)).
           exact (maponpaths dirprod_pr1 p).
      * use funextsec ; intro x.
        use funextsec ; intro x'.
        use hPropUnivalence.
        ** use factor_through_squash ; [ apply propproperty | ].
           intros [ a [ p q ]] ; cbn in *.
           induction p, q.
           apply idpath.
        ** intro p ; cbn in *.
           induction p.
           exact (hinhpr ((x ,, tt) ,, idpath _ ,, idpath _)).
  - split4.
    + intros X Y Z₁ Z₂ R.
      use funextsec ; intro x.
      induction x as [ [ x y ] z ].
      use funextsec ; intro x'.
      induction x' as [ x' [ y' z' ]].
      use hPropUnivalence.
      ** use factor_through_squash ; [ apply propproperty | ].
         intros ((a & b & c) & ( p₁ & p₂ & p₃ ) & ( p₄ & p₅ & p₆ )).
         cbn in *.
         induction p₁, p₂, p₃, p₄, p₅.
         refine (hinhpr (((x ,, y) ,, z') ,, _)).
         repeat split ; try (apply idpath).
         exact p₆.
      ** use factor_through_squash ; [ apply propproperty | ].
         cbn.
         intros (((a & b) & c) & (p₁ & p₂) & p₃ & p₄ & p₅) ; cbn in *.
         induction p₃, p₄, p₅.
         refine (hinhpr ((x ,, y ,, z) ,, _)) ; cbn.
         repeat split ; try (apply idpath).
         *** exact (maponpaths dirprod_pr1 p₁).
         *** exact (maponpaths dirprod_pr2 p₁).
         *** exact p₂.
    + intros X Y₁ Y₂ Z R.
      use funextsec ; intro x.
      induction x as [ [ x y ] z ].
      use funextsec ; intro x'.
      induction x' as [ x' [ y' z' ]].
      use hPropUnivalence.
      ** use factor_through_squash ; [ apply propproperty | ].
         intros ((a & b & c) & ((p₁ & p₂ & p₃) & (p₄ & p₅))) ; cbn in *.
         induction p₁, p₂, p₃.
         refine (hinhpr (((x' ,, y') ,, z) ,, _)) ; cbn.
         repeat split ; try (apply idpath).
         *** exact (maponpaths dirprod_pr1 p₄).
         *** exact p₅.
         *** exact (maponpaths dirprod_pr2 p₄).
      ** use factor_through_squash ; [ apply propproperty | ].
         intros (((a & b) & c) & ((p₁ & p₂ & p₃) & (p₄ & p₅ & p₆))) ; cbn in *.
         induction p₁, p₂, p₄, p₅, p₆.
         refine (hinhpr ((x ,, y ,, z) ,, _)).
         repeat split ; try (apply idpath).
         exact p₃.
    + intros X₁ X₂ Y Z R.
      use funextsec ; intro x.
      induction x as [ [ x y ] z ].
      use funextsec ; intro x'.
      induction x' as [ x' [ y' z' ]].
      use hPropUnivalence.
      ** use factor_through_squash ; [ apply propproperty | ].
         intros ((a & b & c) & ((p₁ & p₂ & p₃) & (p₄ & p₅ & p₆))) ; cbn in *.
         induction p₁, p₂, p₃, p₄, p₅.
         refine (hinhpr (((x ,, y') ,, z) ,, _)) ; cbn.
         repeat split ; try (apply idpath).
         exact p₆.
      ** use factor_through_squash ; [ apply propproperty | ].
         intros (((a & b) & c) & ((p₁ & p₂ & p₃) & (p₄ & p₅ & p₆))) ; cbn in *.
         induction p₁, p₂, p₄, p₅, p₆.
         refine (hinhpr ((x ,, y ,, z) ,, _)).
         repeat split ; try (apply idpath).
         exact p₃.
    + intros X Y Z.
      split.
      * use funextsec ; intro x.
        induction x as [[ x y ] z ].
        use funextsec ; intro x'.
        induction x' as [[ x' y' ] z' ].
        use hPropUnivalence.
        ** use factor_through_squash ; [ apply propproperty | ].
           intros ((a & b & c) & (p₁ & p₂ & p₃) & (p₄ & p₅ & p₆)) ; cbn in *.
           induction p₁, p₂, p₃, p₄, p₅, p₆.
           apply idpath.
        ** cbn ; intro p.
           refine (hinhpr ((x' ,, (y' ,, z')) ,, _)) ; cbn.
           repeat split ; try (apply idpath).
           *** exact (maponpaths dirprod_pr1 (maponpaths dirprod_pr1 p)).
           *** exact (maponpaths dirprod_pr2 (maponpaths dirprod_pr1 p)).
           *** exact (maponpaths dirprod_pr2 p).
      * use funextsec ; intro x.
        induction x as [ x [ y z ]].
        use funextsec ; intro x'.
        induction x' as [ x' [ y' z' ]].
        use hPropUnivalence.
        ** use factor_through_squash ; [ apply propproperty | ].
           intros (((a & b) & c) & (p₁ & p₂ & p₃) & (p₄ & p₅ & p₆)) ; cbn in *.
           induction p₁, p₂, p₃, p₄, p₅, p₆.
           apply idpath.
        ** cbn ; intro p.
           refine (hinhpr (((x ,, y) ,, z) ,, _)) ; cbn.
           repeat split ; try (apply idpath).
           *** exact (maponpaths dirprod_pr1 p).
           *** exact (maponpaths dirprod_pr1 (maponpaths dirprod_pr2 p)).
           *** exact (maponpaths dirprod_pr2 (maponpaths dirprod_pr2 p)).
  - intros X Y.
    use funextsec ; intro x.
    induction x as [ [ x [] ] y ].
    use funextsec ; intro x'.
    induction x' as [ x' y' ].
    use hPropUnivalence.
    + use factor_through_squash ; [ apply propproperty | ] ; cbn.
      intros ( (a & [] & b) & ((p₁ & p₂ & p₃) & (p₄ & p₅)) ) ; cbn in *.
      induction p₁, p₃, p₄, p₅.
      split ; apply idpath.
    + intros [ p q ] ; cbn in *.
      induction p, q.
      refine (hinhpr ((x ,, (tt ,, y)) ,, _)) ; cbn.
      repeat split ; apply idpath.
  - intros W X Y Z.
    use funextsec ; intros (((w & x) & y) & z).
    use funextsec ; intros (w' & x' & y' & z').
    use hPropUnivalence.
    + use factor_through_squash ; [ apply propproperty | ].
      intros ((a & (b & c) & d) & (p₁ & p₂ & p₃ & p₄ & p₅)).
      cbn in p₂, p₃, p₄, p₅.
      induction p₂, p₃, p₄, p₅.
      use (factor_through_squash _ _ p₁) ; [ apply propproperty | ] ; clear p₁ ; cbn.
      intros (((a' & b' & c') & d') & ((p₁ & p₂ & p₃ & p₄) & (p₅ & p₆ & p₇))) ; cbn in *.
      induction p₁, p₂, p₃, p₄, p₅, p₇.
      refine (hinhpr (((w ,, x) ,, (y ,, z)) ,, _)) ; cbn.
      repeat split ; try (apply idpath).
      * exact (maponpaths dirprod_pr1 p₆).
      * apply maponpaths_2.
        exact (maponpaths dirprod_pr2 p₆).
    + use factor_through_squash ; [ apply propproperty | ].
      intros (((a & b) & c & d) & ((p₁ & p₂ & p₃) & (p₄ & p₅ & p₆))) ; cbn in *.
      induction p₂, p₃, p₄, p₅.
      refine (hinhpr ((w ,, ((x ,, y) ,, z)) ,, hinhpr (((w ,, (x ,, y)) ,, z) ,, _) ,, _)) ;
        cbn ;
        repeat split.
      * exact (maponpaths dirprod_pr1 p₁).
      * exact (maponpaths dirprod_pr2 p₁).
      * exact (maponpaths dirprod_pr1 p₆).
      * exact (maponpaths dirprod_pr2 p₆).
Qed.

Definition monoidal_REL
  : monoidal REL
  := monoidal_data_REL ,, monoidal_laws_REL.

Definition REL_monoidal_cat
  : monoidal_cat
  := REL ,, monoidal_REL.

(**
 2. It is symmetric
 *)
Definition REL_braiding
           (X Y : hSet)
  : bin_hrel (X × Y)%set (Y × X)%set
  := (λ xy yx, pr1 xy = pr2 yx ∧ pr2 xy = pr1 yx)%logic.

Proposition REL_braiding_laws
  : sym_mon_cat_laws_tensored REL_monoidal_cat REL_braiding.
Proof.
  repeat split.
  - intros X Y.
    use funextsec ; intro xy₁.
    induction xy₁ as [ y₁ x₁ ].
    use funextsec ; intro xy₂.
    induction xy₂ as [ y₂ x₂ ] ; cbn.
    use hPropUnivalence.
    + use factor_through_squash ; [ apply propproperty | ].
      intros [ y [ [ p₁ p₂ ] [ q₁ q₂ ]]] ; cbn in *.
      induction y as [ a b ] ; cbn in *.
      induction p₁, p₂, q₁, q₂.
      apply idpath.
    + intros p.
      refine (hinhpr ((_ ,, _) ,, ((idpath _ ,, idpath _) ,, (_ ,, _)))) ; cbn.
      * exact (maponpaths dirprod_pr2 p).
      * exact (maponpaths dirprod_pr1 p).
  - intros X₁ X₂ Y₁ Y₂ R₁ R₂.
    use funextsec ; intro xy₁.
    induction xy₁ as [ y₁ x₁ ].
    use funextsec ; intro xy₂.
    induction xy₂ as [ y₂ x₂ ].
    use hPropUnivalence.
    + use factor_through_squash ; [ apply propproperty | ].
      intros [ [ a b ] [ p [ q₁ q₂ ]]] ; cbn in q₁, q₂.
      induction q₁, q₂.
      use (factor_through_squash _ _ p) ; [ apply propproperty | ] ; cbn ; clear p.
      intros [ [ c d ] [ [ p₁ p₂ ] [ q₁ q₂ ] ]].
      apply hinhpr ; cbn in *.
      induction p₁, q₁.
      refine ((x₁ ,, y₁) ,, ((idpath _ ,, idpath _) ,, hinhpr _)) ; cbn.
      refine ((b ,, y₁) ,, ((idpath _ ,, _) ,, (idpath _ ,, _))) ; cbn.
      * exact q₂.
      * exact p₂.
    + use factor_through_squash ; [ apply propproperty | ].
      intros [ [ a b ] [ [ p₁ p₂ ] q]] ; cbn in p₁, p₂.
      induction p₁, p₂.
      use (factor_through_squash _ _ q) ; [ apply propproperty | ] ; cbn ; clear q.
      intros [ [ c d ] [ [ p₁ p₂ ] [ q₁ q₂ ] ]].
      apply hinhpr ; cbn in *.
      induction p₁, q₁.
      refine ((x₂ ,, c) ,, (hinhpr _ ,, (idpath _ ,, idpath _))) ; cbn.
      refine ((x₂ ,, x₁) ,, ((idpath _ ,, _) ,, (idpath _ ,, _))) ; cbn.
      * exact q₂.
      * exact p₂.
  - intros X Y Z.
    use funextsec ; intro xy₁.
    induction xy₁ as [ [ x₁ y₁ ] z₁ ].
    use funextsec ; intro xy₂.
    induction xy₂ as [ y₂ [ z₂ x₂ ]].
    use hPropUnivalence.
    + use factor_through_squash ; [ apply propproperty | ].
      intros ( ((y & z) & x) & q & p₁ & p₂ & p₃).
      cbn in p₁, p₂, p₃.
      induction p₁, p₂, p₃.
      use (factor_through_squash _ _ q) ; [ apply propproperty | ] ; cbn ; clear q.
      intros ( (a & b & c) & ( p₁ & ( p₂ & p₃ ) ) & ( p₄ & p₅ ) ).
      cbn in *.
      induction p₁, p₂, p₃, p₄.
      refine (hinhpr ((y ,, x₁ ,, z) ,, hinhpr _ ,, hinhpr _)).
      * refine (((y ,, x₁) ,, z) ,, hinhpr (((y ,, x₁) ,, z) ,, _) ,, _) ;
          repeat split ;
          try (apply idpath) ; cbn.
        ** exact (maponpaths dirprod_pr2 p₅).
        ** exact (maponpaths dirprod_pr1 p₅).
      * refine ((y ,, (x₁ ,, z)) ,, ((_ ,, _) ,, (_ ,, (_ ,, _)))) ; apply idpath.
    + use factor_through_squash ; [ apply propproperty | ].
      intros ((a & b & c) & (p₁ & p₂)).
      use (factor_through_squash _ _ p₁) ; [ apply propproperty | ] ; clear p₁.
      intros (((a' & b') & c') & (q₁ & q₂ & q₃ & q₄)).
      cbn in q₂, q₃, q₄.
      induction q₂, q₃, q₄.
      use (factor_through_squash _ _ p₂) ; [ apply propproperty | ] ; clear p₂.
      intros ((a'' & b'' & c'') & ((r₁ & r₂) & (r₃ & r₄ & r₅))).
      cbn in r₁, r₂, r₃, r₄, r₅.
      induction r₂, r₃, r₄, r₅.
      use (factor_through_squash _ _ q₁) ; [ apply propproperty | ] ; clear q₁.
      intros (((a''' & b''') & c''') & ((s₁ & s₂ & s₃) & s₄ & s₅)) ; cbn in *.
      induction s₁, s₂, s₃, s₅.
      refine (hinhpr (((y₁ ,, z₁) ,, x₁) ,, hinhpr ((x₁ ,, (y₁ ,, z₁)) ,, _) ,, _)) ;
        cbn ;
        repeat split ;
        try (apply idpath).
      * exact (maponpaths dirprod_pr1 s₄).
      * exact (maponpaths dirprod_pr2 r₁).
      * exact (maponpaths dirprod_pr2 s₄ @ maponpaths dirprod_pr1 r₁).
Qed.

Definition symmetric_REL_monoidal_cat
  : symmetric REL_monoidal_cat.
Proof.
  use make_symmetric.
  - exact REL_braiding.
  - exact REL_braiding_laws.
Defined.

Definition REL_sym_monoidal_cat
  : sym_monoidal_cat
  := REL_monoidal_cat ,, symmetric_REL_monoidal_cat.

(**
 3. It is monoidal closed
 *)
Definition REL_sym_mon_closed_cat
  : sym_mon_closed_cat.
Proof.
  use make_sym_mon_closed_cat.
  - exact REL_sym_monoidal_cat.
  - exact (λ X Y, X × Y)%set.
  - exact (λ X Y xyx y, pr11 xyx = pr2 xyx ∧ pr21 xyx = y)%logic.
  - exact (λ X Y Z R z xy, R (z ,, pr1 xy) (pr2 xy)).
  - intros X Y Z R.
    use funextsec ; intros (z₁ & x₁).
    use funextsec ; intro y₁.
    use hPropUnivalence.
    + abstract
        (use factor_through_squash ; [ apply propproperty | ] ;
         intros (((x₂ & y₂) & x₃) & (q & p₁ & p₂)) ; cbn in p₁, p₂ ;
         induction p₁, p₂ ;
         use (factor_through_squash _ _ q) ; [ apply propproperty | ] ; clear q ; cbn ;
         intros (((x₄ & y₃) & x₅) & ((p₁ & p₂) & p₃ & p₄)) ; cbn in * ;
         induction p₁, p₄ ;
         pose (maponpaths dirprod_pr1 p₃) as r₁ ;
         pose (maponpaths dirprod_pr2 p₃) as r₂ ;
         cbn in r₁, r₂ ;
         rewrite <- r₁, <- r₂ ;
         exact p₂).
    + abstract
        (intro r ;
         refine (hinhpr (((x₁ ,, y₁) ,, x₁) ,, _)) ;
         repeat split ; try (apply idpath) ;
         refine (hinhpr (((x₁ ,, y₁) ,, x₁) ,, _)) ; cbn ;
         repeat split ; try (apply idpath) ;
         exact r).
  - intros X Y Z R.
    use funextsec ; intro z.
    use funextsec ; intros (x & y).
    use hPropUnivalence.
    + abstract
        (intro r ;
         refine (hinhpr (((x ,, y) ,, x) ,, _)) ;
         repeat split ; try (apply idpath) ;
         refine (hinhpr (((x ,, y) ,, x) ,, _)) ;
         repeat split ; try (apply idpath) ; cbn ;
         exact r).
    + abstract
        (use factor_through_squash ; [ apply propproperty | ] ;
         intros (((x₂ & y₂) & x₃) & (q & p₁ & p₂)) ; cbn in p₁, p₂ ;
         induction p₁, p₂ ;
         use (factor_through_squash _ _ q) ; [ apply propproperty | ] ; clear q ; cbn ;
         intros (((x₄ & y₃) & x₅) & ((p₁ & p₂) & p₃ & p₄)) ; cbn in * ;
         induction p₁, p₄ ;
         pose (maponpaths dirprod_pr1 p₃) as r₁ ;
         pose (maponpaths dirprod_pr2 p₃) as r₂ ;
         cbn in r₁, r₂ ;
         rewrite <- r₁, <- r₂ ;
         exact p₂).
Defined.
