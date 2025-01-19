(*************************************************************************************

 Transport laws for strict 2-sided displayed categories

 This file is a collection of various lemmas that are about transporting along paths
 in (possibly strict) 2-sided displayed category.

 Note that we give two laws about composition and `idtoiso`. First of all, we have
 [idtoiso_twosided_disp_concat]. This law holds in arbitrary 2-sided displayed
 categories, and we formulate it purely in the case for paths lying over the identity.
 Second of all, we have [idtoiso_twosided_disp_concat_strict]. This one assumes that
 the 2-sided displayed category is strict. This allows us to formulate the law more
 generally: we look at morphisms lying over any two paths `x = x` and `y = y`, and
 the result lies over two identity paths.

 Finally, we also define a transport operation for paths of objects. This operation is
 useful when working with strict 2-sided displayed categories. That is because in that
 case, one frequently meets paths of objects.

 Contents
 1. Identity, inverse, and composition
 2. Composition in a strict 2-sided displayed category
 3. A special law for composition assuming strictness
 4. Transporting along paths of objects

 *************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.

Local Open Scope cat.

(** * 1. Identity, inverse, and composition *)
Proposition idtoiso_twosided_disp_identity
            {C₁ C₂ : category}
            {D : strict_twosided_disp_cat C₁ C₂}
            {x : C₁}
            {y : C₂}
            {xy : D x y}
            (p : xy = xy)
  : pr1 (idtoiso_twosided_disp (idpath _) (idpath _) p)
    =
    id_two_disp xy.
Proof.
  assert (p = idpath _) as s.
  {
    apply is_strict_strict_twosided_disp_cat.
  }
  rewrite s.
  apply idpath.
Qed.

Proposition idtoiso_twosided_disp_inv
            {C₁ C₂ : category}
            {D : twosided_disp_cat C₁ C₂}
            {x : C₁}
            {y : C₂}
            {xy xy' : D x y}
            (p : xy = xy')
  : pr1 (idtoiso_twosided_disp (idpath _) (idpath _) (!p))
    =
    iso_inv_twosided_disp (idtoiso_twosided_disp (idpath _) (idpath _) p).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition idtoiso_twosided_disp_concat
            {C₁ C₂ : category}
            {D : twosided_disp_cat C₁ C₂}
            {x : C₁}
            {y : C₂}
            {xy₁ xy₂ xy₃ : D x y}
            (p : xy₁ = xy₂)
            (q : xy₂ = xy₃)
  : pr1 (idtoiso_twosided_disp (idpath x) (idpath y) p)
    ;;2
    pr1 (idtoiso_twosided_disp (idpath x) (idpath y) q)
    =
    transportb_disp_mor2
      (id_left _)
      (id_left _)
      (pr1 (idtoiso_twosided_disp (idpath x) (idpath y) (p @ q))).
Proof.
  induction p, q ; cbn.
  rewrite id_two_disp_left.
  apply idpath.
Qed.

Proposition idtoiso_twosided_disp_concat'
            {C₁ C₂ : category}
            {D : twosided_disp_cat C₁ C₂}
            {x : C₁}
            {y : C₂}
            {xy₁ xy₂ xy₃ : D x y}
            (p : xy₁ = xy₂)
            (q : xy₂ = xy₃)
  : pr1 (idtoiso_twosided_disp (idpath x) (idpath y) (p @ q))
    =
    transportf_disp_mor2
      (id_left _)
      (id_left _)
      (pr1 (idtoiso_twosided_disp (idpath x) (idpath y) p)
       ;;2
       pr1 (idtoiso_twosided_disp (idpath x) (idpath y) q)).
Proof.
  induction p, q ; cbn.
  rewrite id_two_disp_left.
  rewrite transportfb_disp_mor2.
  apply idpath.
Qed.

Proposition idtoiso_twosided_disp_functor
            {C₁ C₁' C₂ C₂' : category}
            {F : C₁ ⟶ C₁'}
            {G : C₂ ⟶ C₂'}
            {D : twosided_disp_cat C₁ C₂}
            {D' : twosided_disp_cat C₁' C₂'}
            (FG : twosided_disp_functor F G D D')
            {x : C₁} {y : C₂}
            {xy xy' : D x y}
            (p : xy = xy')
  : pr1 (idtoiso_twosided_disp
           (idpath (F x)) (idpath (G y))
           (maponpaths (λ xy, FG x y xy) p))
    =
    transportf_disp_mor2
      (functor_id F _)
      (functor_id G _)
      (#2 FG (idtoiso_twosided_disp (idpath x) (idpath y) p)).
Proof.
  induction p ; cbn.
  rewrite twosided_disp_functor_id.
  rewrite transportfb_disp_mor2.
  apply idpath.
Qed.

Proposition idtoiso_twosided_disp_functor'
            {C₁ C₁' C₂ C₂' : category}
            {F : C₁ ⟶ C₁'}
            {G : C₂ ⟶ C₂'}
            {D : twosided_disp_cat C₁ C₂}
            {D' : twosided_disp_cat C₁' C₂'}
            (FG : twosided_disp_functor F G D D')
            {x : C₁} {y : C₂}
            {xy xy' : D x y}
            (p : xy = xy')
  : #2 FG (idtoiso_twosided_disp (idpath x) (idpath y) p)
    =
    transportb_disp_mor2
      (functor_id F _)
      (functor_id G _)
      (pr1 (idtoiso_twosided_disp
              (idpath (F x)) (idpath (G y))
              (maponpaths (λ xy, FG x y xy) p))).
Proof.
  induction p ; cbn.
  rewrite twosided_disp_functor_id.
  apply idpath.
Qed.

(** * 2. Composition in a strict 2-sided displayed category *)
Proposition idtoiso_twosided_disp_triple_concat
            {C₁ C₂ : category}
            {D : strict_twosided_disp_cat C₁ C₂}
            {x x' : C₁}
            {f : x --> x'}
            {y y' : C₂}
            {g : y --> y'}
            {xy wxy : D x y}
            (p p' : wxy = xy)
            {xy' wxy' : D x' y'}
            (q q' : xy' = wxy')
            (fg : xy -->[ f ][ g ] xy')
  : idtoiso_twosided_disp (idpath x) (idpath y) p
    ;;2 fg
    ;;2 idtoiso_twosided_disp (idpath x') (idpath y') q
    =
    idtoiso_twosided_disp (idpath x) (idpath y) p'
    ;;2 fg
    ;;2 idtoiso_twosided_disp (idpath x') (idpath y') q'.
Proof.
  assert (p = p') as s.
  {
    apply is_strict_strict_twosided_disp_cat.
  }
  rewrite s ; clear s.
  assert (q = q') as s.
  {
    apply is_strict_strict_twosided_disp_cat.
  }
  rewrite s ; clear s.
  apply idpath.
Qed.

(** * 3. A special law for composition assuming strictness *)
Proposition idtoiso_twosided_disp_concat_disp_path
            {C₁ C₂ : setcategory}
            {D : strict_twosided_disp_cat C₁ C₂}
            {x : C₁}
            {rx rx' : x = x}
            {y : C₂}
            {ry ry' : y = y}
            {xy₁ xy₂ xy₃ : D x y}
            (p : transportf
                   (λ z, D z y)
                   rx
                   (transportf
                      (λ z, D x z)
                      ry
                      xy₁)
                 =
                 xy₂)
            (q : transportf
                   (λ z, D z y)
                   rx'
                   (transportf
                      (λ z, D x z)
                      ry'
                      xy₂)
                 =
                 xy₃)
  : xy₁ = xy₃.
Proof.
  assert (rx = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s in p ; clear s.
  assert (rx' = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s in q ; clear s.
  assert (ry = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s in p ; clear s.
  assert (ry' = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s in q ; clear s.
  cbn in p, q ; cbn.
  rewrite p, q.
  apply idpath.
Qed.

Proposition idtoiso_twosided_disp_concat_disp_path_idpath
            {C₁ C₂ : setcategory}
            {D : strict_twosided_disp_cat C₁ C₂}
            {x : C₁}
            {y : C₂}
            (xy : D x y)
  : idtoiso_twosided_disp_concat_disp_path
      (rx := idpath x) (rx' := idpath x)
      (ry := idpath y) (ry' := idpath y)
      (idpath xy)
      (idpath xy)
    =
    idpath xy.
Proof.
  apply is_strict_strict_twosided_disp_cat.
Qed.

Proposition idtoiso_twosided_disp_concat_strict_base_path
            {C : setcategory}
            {x : C}
            (rx rx' : x = x)
  : idtoiso rx · idtoiso rx' = identity _.
Proof.
  assert (rx = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  assert (rx' = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  apply id_left.
Qed.

Proposition idtoiso_twosided_disp_concat_strict
            {C₁ C₂ : setcategory}
            {D : strict_twosided_disp_cat C₁ C₂}
            {x : C₁}
            {rx rx' : x = x}
            {y : C₂}
            {ry ry' : y = y}
            {xy₁ xy₂ xy₃ : D x y}
            (p : transportf
                   (λ z, D z y)
                   rx
                   (transportf
                      (λ z, D x z)
                      ry
                      xy₁)
                 =
                 xy₂)
            (q : transportf
                   (λ z, D z y)
                   rx'
                   (transportf
                      (λ z, D x z)
                      ry'
                      xy₂)
                 =
                 xy₃)
  : pr1 (idtoiso_twosided_disp rx ry p)
    ;;2
    pr1 (idtoiso_twosided_disp rx' ry' q)
    =
    transportb_disp_mor2
      (idtoiso_twosided_disp_concat_strict_base_path rx rx')
      (idtoiso_twosided_disp_concat_strict_base_path ry ry')
      (idtoiso_twosided_disp
         (idpath _) (idpath _)
         (idtoiso_twosided_disp_concat_disp_path p q)).
Proof.
  induction p, q.
  assert (rx = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  assert (rx' = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  assert (ry = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  assert (ry' = idpath _) as s.
  {
    apply isaset_ob.
  }
  rewrite s ; clear s.
  rewrite idtoiso_twosided_disp_concat_disp_path_idpath.
  clear rx rx' ry ry'.
  cbn.
  rewrite (id_two_disp_left (D := D)).
  use transportb_disp_mor2_eq.
  apply idpath.
Qed.

(** * 4. Transporting along paths of objects *)
Definition transportb_disp_ob2
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x x' : C₁}
           (p : x = x')
           {y y' : C₂}
           (q : y = y')
           (xy : D x' y')
  : D x y
  := transportb
       (λ z, D _ z)
       q
       (transportb
          (λ z, D z _)
          p
          xy).

Definition transportb_disp_ob2_mor_path
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x x' : C₁}
           (p : x = x')
           {y y' : C₂}
           (q : y = y')
           (xy : D x' y')
  : transportf
      (λ z, D z y')
      p
      (transportf (λ z, D x z)
         q
         (transportb_disp_ob2 p q xy))
    =
    xy.
Proof.
  induction p, q.
  cbn.
  apply idpath.
Defined.

Definition transportb_disp_ob2_mor
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x x' : C₁}
           (p : x = x')
           {y y' : C₂}
           (q : y = y')
           (xy : D x' y')
  : transportb_disp_ob2 p q xy -->[ idtoiso p ][ idtoiso q ] xy.
Proof.
  refine (idtoiso_twosided_disp _ _ _).
  apply transportb_disp_ob2_mor_path.
Defined.

Definition transportb_disp_ob2_inv_path
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x x' : C₁}
           (p : x = x')
           {y y' : C₂}
           (q : y = y')
           (xy : D x' y')
  : transportf
      (λ z, D z y)
      (!p)
      (transportf (λ z, D x' z)
         (!q)
         xy)
    =
    transportb_disp_ob2 p q xy.
Proof.
  induction p, q.
  cbn.
  apply idpath.
Defined.

Definition transportb_disp_ob2_id_id
           {C₁ C₂ : setcategory}
           {D : twosided_disp_cat C₁ C₂}
           {x : C₁}
           (p : x = x)
           {y : C₂}
           (q : y = y)
           (xy : D x y)
  : transportb_disp_ob2 p q xy = xy.
Proof.
  assert (p = idpath _) as h₁.
  {
    apply C₁.
  }
  assert (q = idpath _) as h₂.
  {
    apply C₂.
  }
  rewrite h₁, h₂ ; cbn.
  apply idpath.
Qed.

Definition transportb_disp_ob2_inv
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x x' : C₁}
           (p : x = x')
           {y y' : C₂}
           (q : y = y')
           (xy : D x' y')
  : xy -->[ idtoiso (!p) ][ idtoiso (!q) ] transportb_disp_ob2 p q xy.
Proof.
  refine (idtoiso_twosided_disp _ _ _).
  apply transportb_disp_ob2_inv_path.
Defined.
