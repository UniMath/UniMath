(** * Double Categories
 
  Authors: Benedikt Ahrens, Paige North, Nima Rasekh, Niels van der Weide
  June 2023
  Based on definition of weak double category in Section 3.3 of the book Higher Dimensional Categories by Marco Grandis.
 *)


(** ** Contents :

  - Define a pre double category as a ``weak double category`` in the sense of Grandis. 
    This means one direction is weak and the other direction is strict.
    
  - Double categories: A double category is a pre-double category with two set-truncated hom sets.
  - 
  - Univalent Double Categories: A univalent double category is a double category with two univalent underlying categories. 

  - The structure is defined from scratch rather than building on a category. 
    This makes further generalizations easier.
 *)

  Require Import UniMath.Foundations.Propositions.
  Require Import UniMath.Foundations.Sets.
  Require Import UniMath.MoreFoundations.PartA.
  Require Import UniMath.MoreFoundations.Notations.
  Require Import UniMath.CategoryTheory.Core.Prelude.


Section Definition_of_Double_Graphs.
(*  Definition of a double graph.*)  

Definition predoublecategory_ob_mor_hor : UU
:= ∑ obdb : UU, obdb -> obdb -> UU. 

Definition obdb (C : predoublecategory_ob_mor_hor) : UU := @pr1 _ _ C.

Coercion obdb : predoublecategory_ob_mor_hor >-> UU.

Definition predoublecategory_mor_ver (C : predoublecategory_ob_mor_hor) 
  : UU
  := (C -> C -> UU).

Definition predoublecategory_ob_mor_data : UU :=
  ∑ C, predoublecategory_mor_ver C.

Coercion precategory_ob_mor_from_predoublecategory_ob_mor_data (C : predoublecategory_ob_mor_data) :
    predoublecategory_ob_mor_hor := pr1 C.

End Definition_of_Double_Graphs.

Section Morphism_Helper_Functions. (* Couple helper functions for Approach 1 *)

Definition get_predoublecat_hor_mor (C: predoublecategory_ob_mor_data) : C → C → UU 
  := pr21 C.

Definition get_predoublecat_ver_mor (C: predoublecategory_ob_mor_data) : C → C → UU 
:= pr2 C.

End Morphism_Helper_Functions.

Notation "x '-h->' y" := (get_predoublecat_hor_mor _ x y) (at level 60).
Notation "x '-v->' y" := (get_predoublecat_ver_mor _ x y) (at level 60).
  

Section Underlying_Horizontal_Category.
  (* Now we construct the horizontal category.
     This is independent from squares. 
     From here on we will take strictness in one direction for granted. *)

(* Here we can take two approaches:
1)  Take the ``underlying precategory`` and use the existing category definitions. 
    This one is easier, but less generalizable.
2)  Define everything from scratch.
    This one is much more pain, but offers a more straightforward path for generalization.

I wrote the first and kept it in a separate file. The second one is kept here.
*)

Definition predoublecategory_hor_id_comp  (C : predoublecategory_ob_mor_data): UU (* Horizontal category data*)
  :=
    (∏ c : C, c -h-> c) (* identities *)
      ×
    (∏ a b c : C, a -h-> b -> b -h-> c -> a -h-> c). (* composition *)

Definition predoublecategory_hor_precat_data : UU
     := ∑ C : predoublecategory_ob_mor_data, predoublecategory_hor_id_comp C.
  
Definition predoublecategory_ob_mor_data_from_predoublecategory_hor_precat_data (C: predoublecategory_hor_precat_data) : 
  predoublecategory_ob_mor_data := pr1 C.

  Coercion predoublecategory_ob_mor_data_from_predoublecategory_hor_precat_data :
  predoublecategory_hor_precat_data >->  predoublecategory_ob_mor_data. 

Definition hor_identity {C : predoublecategory_hor_precat_data} 
     : ∏ c : C, c -h-> c
     := pr1 (pr2 C).
   
Definition hor_compose {C : predoublecategory_hor_precat_data} { a b c : C }
     : a -h-> b -> b -h-> c -> a -h-> c
     := pr2 (pr2 C) a b c.

Notation "f ·h g" := (hor_compose f g) (at level 60).
Notation "g ∘h f" := (hor_compose f g) (at level 60).
     
Definition is_predoublecategory_hor (C : predoublecategory_hor_precat_data) : UU (* Horizontal Category Condition *)
     :=
       ((∏ (a b : C) (f : a -h-> b), hor_identity a ·h f = f)
        ×
        (∏ (a b : C) (f : a -h-> b), f ·h hor_identity b = f))
       ×
       ((∏ (a b c d : C) (f : a -h-> b) (g : b -h-> c) (h : c -h-> d), f ·h (g ·h h) = (f ·h g) ·h h)
          ×
        (∏ (a b c d : C) (f : a -h-> b) (g : b -h-> c) (h : c -h-> d), (f ·h g) ·h h = f ·h (g ·h h))).


Definition predoublecategory_hor: UU := total2 is_predoublecategory_hor. (* horizontal precategory*)

Definition make_predoublecategory_hor (C : predoublecategory_hor_precat_data) (H : is_predoublecategory_hor C)
  : predoublecategory_hor
  := tpair _ C H.

Definition predoublecategory_hor_data_from_predoublecategory_hor (C : predoublecategory_hor) :
  predoublecategory_hor_precat_data := pr1 C.
Coercion predoublecategory_hor_data_from_predoublecategory_hor : predoublecategory_hor >-> predoublecategory_hor_precat_data.
   
Definition get_id_hor_left (C : predoublecategory_hor) :
  ∏ (a b : C) (f : a -h-> b),
          hor_identity a ·h f = f := pr112 C.

Definition id_hor_left {C : predoublecategory_hor} {a b : C} (f: a -h-> b) : hor_identity a ·h f = f 
  :=  get_id_hor_left C a b f.
  
Definition get_id_hor_right (C : predoublecategory_hor) :
  ∏ (a b : C) (f : a -h-> b),
          f ·h hor_identity b = f := pr212 C.

Definition id_hor_right {C : predoublecategory_hor} {a b : C} (f: a -h-> b) : f  ·h hor_identity b = f 
    :=  get_id_hor_right C a b f.
          
Definition get_assoc_hor (C : predoublecategory_hor) :
  ∏ (a b c d : C)
         (f : a -h-> b) (g : b -h-> c) (h : c -h-> d),
                    f ·h (g ·h h) = (f ·h g) ·h h := pr122 C.

Definition assoc_hor {C : predoublecategory_hor} {a b c d : C} (f : a -h-> b) (g : b -h-> c) (h : c -h-> d) : f ·h (g ·h h) = (f ·h g) ·h h
  := get_assoc_hor C a b c d f g h.

Definition und_ob_hor_ob_mor (C : predoublecategory_ob_mor_hor) : precategory_ob_mor :=
  make_precategory_ob_mor (pr1 C) (pr2 C).

Definition und_ob_hor_precategory_data (C: predoublecategory_hor_precat_data) : precategory_data :=
  make_precategory_data (und_ob_hor_ob_mor C) (pr12 C) (pr22 C).

Definition und_ob_hor_precategory_axioms (C: predoublecategory_hor) : is_precategory (und_ob_hor_precategory_data C) :=
  @make_is_precategory (und_ob_hor_precategory_data C) (pr112 C) (pr212 C) (pr122 C) (pr222 C).

Definition und_ob_hor_precategory (C : predoublecategory_hor) : precategory :=
  make_precategory (und_ob_hor_precategory_data C) (und_ob_hor_precategory_axioms C).

Definition has_hor_homsets (C : predoublecategory_ob_mor_data) : UU := ∏ a b : C, isaset (a -h-> b). (*Horizontal Hom sets *)

Definition doublecategory_hor := ∑ C:predoublecategory_hor, has_hor_homsets C.

Definition make_doublecategory_hor C h : doublecategory_hor := C,,h.

Definition doublecategory_hor_to_predoublecategory_hor : doublecategory_hor -> predoublecategory_hor := pr1.

Coercion doublecategory_hor_to_predoublecategory_hor : doublecategory_hor >-> predoublecategory_hor.

Coercion homset_property (C : doublecategory_hor) : has_hor_homsets C := pr2 C.

Definition und_ob_hor_category (C: doublecategory_hor) : category :=
make_category (und_ob_hor_precategory C) (pr2 C).

End Underlying_Horizontal_Category.

Notation "f ·h g" := (hor_compose f g) (at level 60).
Notation "g ∘h f" := (hor_compose f g) (at level 60).

Section Underlying_Vertical_Composition. 
(* In this section we describe the vertical composition, which does not give us a category.*)

Definition predoublecategory_ver_id_comp (C : predoublecategory_hor) : UU (* Vertical composition data *)
  :=
    (∏ c : C, c -v-> c) (* vertical identities *)
      ×
    (∏ a b c : C, a -v-> b -> b -v-> c -> a -v-> c). (* vertical composition *)

Definition predoublecategory_hor_cat_ver_precat_data : UU (* double graph with horizontal and vertical composition*)
     := ∑ C : predoublecategory_hor, predoublecategory_ver_id_comp C.
  
Definition predoublecategory_hor_from_predoublecategory_hor_cat_ver_precat_data (C: predoublecategory_hor_cat_ver_precat_data) : 
predoublecategory_hor := pr1 C.

Coercion predoublecategory_hor_from_predoublecategory_hor_cat_ver_precat_data :
predoublecategory_hor_cat_ver_precat_data >->  predoublecategory_hor. 

Definition ver_identity {C : predoublecategory_hor_cat_ver_precat_data}
     : ∏ c : C, c -v-> c
     := pr1 (pr2 C).

Definition ver_compose {C : predoublecategory_hor_cat_ver_precat_data} { a b c : C }
     : a -v-> b -> b -v-> c -> a -v-> c
     := pr2 (pr2 C) a b c.

End Underlying_Vertical_Composition. 

Notation "f ·v g" := (ver_compose f g) (at level 60).
Notation "g ∘v f" := (ver_compose f g) (at level 60).
Notation "'ver_comp' C f g" := (@ver_compose C _ _ _ f g) (at level 60).

Section Squares. (* Define Squares and their helper functions *)
  
 Definition predoublecategory_square (C : predoublecategory_hor_cat_ver_precat_data) : UU
 := ∏ (a b c d : C) (f: a -h-> b) (g: a -v-> c) (h: b -v-> d) (k: c -h-> d), UU.
   
Definition predoublecategory_ob_mor_sq_data : UU := (*Ob, HorMor, VerMor, Sq hor ver compositions*)
   ∑ C, predoublecategory_square C.

Definition predoublecategory_hor_cat_ver_precat_data_from_predoublecategory_square (C : predoublecategory_ob_mor_sq_data) :
predoublecategory_hor_cat_ver_precat_data := pr1 C. (* Forget Sq *)

Coercion predoublecategory_hor_cat_ver_precat_data_from_predoublecategory_square :
predoublecategory_ob_mor_sq_data >-> predoublecategory_hor_cat_ver_precat_data.

 Definition get_predoublecat_sq (C: predoublecategory_ob_mor_sq_data) : 
 ∏ (a b c d : C) (f: a -h-> b)  (g: a -v-> c) (h: b -v-> d) (k: c -h-> d), UU 
   := pr2 C. 

Definition hom_sq_between_ver (C: predoublecategory_ob_mor_sq_data) {a b c d : C} (g: a -v-> c) (h: b -v-> d): UU
  := ∑ (f: a -h-> b) (k: c -h-> d), (get_predoublecat_sq C a b c d f g h k).

Definition hom_sq_between_hor (C: predoublecategory_ob_mor_sq_data) {a b c d : C} (f: a -h-> b) (k: c -h-> d): UU
  := ∑ (g: a -v-> c) (h: b -v-> d), (get_predoublecat_sq C a b c d f g h k).

Definition sqq {C: predoublecategory_ob_mor_sq_data} 
{a b c d : C} (f: a -h-> b)  (g: a -v-> c) (h: b -v-> d) (k: c -h-> d):  UU 
:= get_predoublecat_sq C a b c d f g h k.

Definition boundary_sq_transport {C : predoublecategory_ob_mor_sq_data}
{ a b c d : C } {f1: a -h-> b} {g1: a -v-> c} {h1: b -v-> d} {k1: c -h-> d}
  {f2: a -h-> b} {g2: a -v-> c} {h2: b -v-> d} {k2: c -h-> d}
    (eqf: f1 = f2) (eqg: g1 = g2) (eqh: h1 = h2) (eqk: k1 = k2)
    (α : sqq f1 g1 h1 k1) : sqq f2 g2 h2 k2 :=
    (transportf (fun k0 : c-h-> d => sqq f2 g2 h2 k0) eqk
    (transportf (fun h0 : b-v-> d => sqq f2 g2 h0 k1) eqh
    (transportf (fun g0 : a-v-> c => sqq f2 g0 h1 k1) eqg 
      (transportf (fun f0 : a-h-> b => sqq f0 g1 h1 k1) eqf α)))).

End Squares.

Notation "'mor_sq'" := (get_predoublecat_sq).
Notation "'Sq[' x '-hv-' f h '-hv->' y , z '-vh-' g k '-vh->' w ]" := 
  (get_predoublecat_sq _ x y z w f g h k) (at level 200, x ident, y ident, z ident, w ident, f ident, g ident, h ident, k ident).   

Section Horizontal_Composition_Squares. 
(*We construct the horizontal composition of squares and study their properties, such as associativity and unitality. *)

Definition predoublecategory_sq_hor_id_comp (C : predoublecategory_ob_mor_sq_data): UU (* Horizontal composition of squares *)
    := 
      (∏ (a b : C) (f: a -v-> b), (sqq (hor_identity a) f f (hor_identity b)))  (* identities *)
        ×
      (∏ (a0 a1 b0 b1 c0 c1 : C) 
      (f0: a0 -v-> a1) (f1: b0 -v-> b1) (f2: c0 -v-> c1) (g0: a0 -h-> b0) (h0: b0 -h-> c0) (g1: a1 -h-> b1) (h1: b1 -h-> c1), 
        (sqq g0 f0 f1 g1) →  
        (sqq h0 f1 f2 h1) →
        (sqq  (g0 ·h h0) f0 f2 (g1 ·h h1)) (* composition *)
      ). 

Definition predoublecategory_sq_hor_data : UU (* Double Graph with Squares horizontal morphism and square composition *)
      := ∑ C : predoublecategory_ob_mor_sq_data, predoublecategory_sq_hor_id_comp C.
    
Definition make_predoublecategory_sq_hor_data (C : predoublecategory_ob_mor_sq_data)
        (id : (∏ (a b : C) (f: a -v-> b), (mor_sq C a a b b (hor_identity a) f f (hor_identity b))))
        (comp:  (∏ (a0 a1 b0 b1 c0 c1 : C) 
        (f0: a0 -v-> a1) (f1: b0 -v-> b1) (f2: c0 -v-> c1) (g0: a0 -h-> b0) (h0: b0 -h-> c0) (g1: a1 -h-> b1) (h1: b1 -h-> c1), 
          (sqq g0 f0 f1 g1) →
          (sqq h0 f1 f2 h1) →
          (sqq (g0 ·h h0) f0 f2 (g1 ·h h1))) )
      : predoublecategory_sq_hor_data
      := tpair _ C (make_dirprod id comp).

Definition predoublecategory_ob_mor_sq_data_from_predoublecategory_sq_hor_data (C : predoublecategory_sq_hor_data) :
predoublecategory_ob_mor_sq_data := pr1 C.
  
Coercion predoublecategory_ob_mor_sq_data_from_predoublecategory_sq_hor_data :
    predoublecategory_sq_hor_data >-> predoublecategory_ob_mor_sq_data.
    
    Definition get_hor_sq_identity {C : predoublecategory_sq_hor_data}
      : (∏ (a b : C) (f: a -v-> b), (sqq (hor_identity a) f f (hor_identity b)))
      := pr1 (pr2 C).
    
    Definition hor_sq_identity {C : predoublecategory_sq_hor_data} {a b: C} (f: a -v-> b) : 
      (sqq (hor_identity a) f f (hor_identity b)) := get_hor_sq_identity a b f.
    
    Definition hor_sq_compose {C : predoublecategory_sq_hor_data} 
    { a0 a1 b0 b1 c0 c1 : C }
    {f0: a0 -v-> a1} {f1: b0 -v-> b1} {f2: c0 -v-> c1} {g0: a0 -h-> b0} {h0: b0 -h-> c0} {g1: a1 -h-> b1} {h1: b1 -h-> c1}
      : (sqq g0 f0 f1 g1) →
      (sqq h0 f1 f2 h1) →
      (sqq (g0 ·h h0) f0 f2 (g1 ·h h1))
      := pr2 (pr2 C) a0 a1 b0 b1 c0 c1 f0 f1 f2 g0 h0 g1 h1.
    
Notation "α ·sqh β" := (hor_sq_compose α β) (at level 60).
Notation "α ∘sqh β" := (hor_sq_compose α β) (at level 60).

(* The next 3 Definitions focus on various base changes along the boundary identities 
   via identity and associativity. *)

Definition hor_trans_id_left_sq {C : predoublecategory_sq_hor_data} 
    { a b c d : C } {f: a -h-> b} {g: a -v-> c} {h: b -v-> d} {k: c -h-> d} 
      (α: sqq ((hor_identity a) ·h f) g h ((hor_identity c) ·h k )) : 
      sqq f g h k
      := boundary_sq_transport (id_hor_left f) (idpath g) (idpath h) (id_hor_left k) α.

Definition hor_trans_id_right_sq {C : predoublecategory_sq_hor_data} 
          { a b c d : C } {f: a -h-> b} {g: a -v-> c} {h: b -v-> d} {k: c -h-> d} 
            (α: sqq (f ·h (hor_identity b)) g h (k ·h (hor_identity d))) : sqq f g h k
            := boundary_sq_transport (id_hor_right f) (idpath g) (idpath h) (id_hor_right k) α.
          
Definition hor_trans_assoc_sq {C : predoublecategory_sq_hor_data}
            { a0 b0 c0 d0 a1 b1 c1 d1 : C } 
            {f0: a0 -h-> b0} {g0: b0 -h-> c0} {h0: c0 -h-> d0}
            {f1: a1 -h-> b1} {g1: b1 -h-> c1} {h1: c1 -h-> d1}
            {ma: a0 -v-> a1}  {md: d0 -v-> d1}
            (α: sqq (f0 ·h (g0 ·h h0)) ma md (f1 ·h (g1 ·h h1))): 
            sqq ((f0 ·h g0) ·h h0) ma md ((f1 ·h g1) ·h h1) 
            := boundary_sq_transport (assoc_hor f0 g0 h0) (idpath ma) (idpath md) (assoc_hor f1 g1 h1) α.

Definition is_predoublecategory_hor_sq (C : predoublecategory_sq_hor_data) : UU (* Data of horizontal composition of squares *)
  :=
    ((∏ (a b c d : C) (f: a -h-> b) (g: a -v-> c) (h: b -v-> d) (k: c -h-> d)
      (α : mor_sq C a b c d f g h k), 
      hor_trans_id_left_sq((hor_sq_identity g) ·sqh α) = α))
     ×
     ((∏ (a b c d : C) (f: a -h-> b) (g: a -v-> c) (h: b -v-> d) (k: c -h-> d)
      (α : mor_sq C a b c d f g h k), 
      hor_trans_id_right_sq(α ·sqh (hor_sq_identity h)) = α))
    ×
    (∏ ( a0 b0 c0 d0 a1 b1 c1 d1 : C ) 
    (f0: a0 -h-> b0) (g0: b0 -h-> c0) (h0: c0 -h-> d0) 
    (f1: a1 -h-> b1) (g1: b1 -h-> c1) (h1: c1 -h-> d1) 
    (ma: a0 -v-> a1) (mb: b0 -v-> b1) (mc: c0 -v-> c1) (md: d0 -v-> d1)
    (α: sqq f0 ma mb f1)
    (β: sqq g0 mb mc g1)
    (γ: sqq h0 mc md h1),
    hor_trans_assoc_sq (α ·sqh (β ·sqh γ)) = (α ·sqh β) ·sqh γ) .

  Definition predoublecategory_hor_sq: UU := total2 is_predoublecategory_hor_sq. 
  (* Double Graph with Squares horizontal morphism and square composition + axioms*)

  Definition make_predoublecategory_hor_sq (C : predoublecategory_sq_hor_data) (H : is_predoublecategory_hor_sq C)
    : predoublecategory_hor_sq
    := tpair _ C H.
  
  Definition predoublecategory_sq_hor_data_from_predoublecategory_hor_sq (C : predoublecategory_hor_sq) :
  predoublecategory_sq_hor_data := pr1 C.
  Coercion predoublecategory_sq_hor_data_from_predoublecategory_hor_sq : predoublecategory_hor_sq >-> predoublecategory_sq_hor_data.
     
  Definition get_id_hor_sq_left (C : predoublecategory_hor_sq) :
  ∏ (a b c d : pr1 C) (f : a -h-> b) (g : a -v-> c) (h : b -v-> d) (k : c -h-> d) 
      (α : sqq f g h k), hor_trans_id_left_sq ((hor_sq_identity g) ·sqh α) = α := pr12 C.

  Definition id_hor_sq_left {C : predoublecategory_hor_sq}  
  {a b c d : pr1 C} {f : a -h-> b} {g : a -v-> c} {h : b -v-> d} {k : c -h-> d} (α : sqq f g h k)
    : hor_trans_id_left_sq ((hor_sq_identity g) ·sqh α) = α
    := get_id_hor_sq_left C a b c d f g h k α.

  Definition get_id_hor_sq_right (C : predoublecategory_hor_sq) :
  ∏ (a b c d : pr1 C) (f : a -h-> b) (g : a -v-> c) (h : b -v-> d) (k : c -h-> d) 
    (α : sqq f g h k), hor_trans_id_right_sq (α ·sqh (hor_sq_identity h)) = α := pr122 C.
  
  Definition id_hor_sq_right {C : predoublecategory_hor_sq}  
  {a b c d : pr1 C} {f : a -h-> b} {g : a -v-> c} {h : b -v-> d} {k : c -h-> d} (α : sqq f g h k)
    : hor_trans_id_right_sq (α ·sqh (hor_sq_identity h)) = α
    := get_id_hor_sq_right C a b c d f g h k α.
  
  Definition get_assoc_sq_hor (C : predoublecategory_hor_sq) :
  ∏ (a0 b0 c0 d0 a1 b1 c1 d1 : C ) 
    (f0: a0 -h-> b0) (g0: b0 -h-> c0) (h0: c0 -h-> d0) 
    (f1: a1 -h-> b1) (g1: b1 -h-> c1) (h1: c1 -h-> d1) 
    (ma: a0 -v-> a1) (mb: b0 -v-> b1) (mc: c0 -v-> c1) (md: d0 -v-> d1)
    (α: sqq f0 ma mb f1)
    (β: sqq g0 mb mc g1)
    (γ: sqq h0 mc md h1),
    hor_trans_assoc_sq (α ·sqh (β ·sqh γ)) = (α ·sqh β) ·sqh γ := pr222 C.
  
    Definition assoc_sq_hor {C : predoublecategory_hor_sq}  
    {a0 b0 c0 d0 a1 b1 c1 d1 : pr1 C} {f0: a0 -h-> b0} {g0: b0 -h-> c0} {h0: c0 -h-> d0} 
      {f1: a1 -h-> b1} {g1: b1 -h-> c1} {h1: c1 -h-> d1} 
      {ma: a0 -v-> a1} {mb: b0 -v-> b1} {mc: c0 -v-> c1} {md: d0 -v-> d1}
        (α: sqq f0 ma mb f1)
        (β: sqq g0 mb mc g1)
        (γ: sqq h0 mc md h1)
      : hor_trans_assoc_sq (α ·sqh (β ·sqh γ)) = (α ·sqh β) ·sqh γ
      := get_assoc_sq_hor C a0 b0 c0 d0 a1 b1 c1 d1 f0 g0 h0 f1 g1 h1 ma mb mc md α β γ.
  
End Horizontal_Composition_Squares.

Notation "α ·sqh β" := (hor_sq_compose α β) (at level 60).
Notation "α ∘sqh β" := (hor_sq_compose α β) (at level 60).

Section Special_Iso_Squares. (* Define special iso squres which are necessary for the vertical composition *)

Definition get_predoublecat_sq_special {C: predoublecategory_ob_mor_sq_data} {a b : C} (g: a -v-> b) (h: a -v-> b): UU 
  := sqq (hor_identity a) g h (hor_identity b).
  
  
Definition is_iso_square {C: predoublecategory_sq_hor_data} {a b : C} {g: a -v-> b} {h: a -v-> b} 
  (α : get_predoublecat_sq_special g h): UU 
  := ∑ (β : get_predoublecat_sq_special h g) 
       (γ : get_predoublecat_sq_special h g), 
  (hor_trans_id_right_sq (α ·sqh β) = (hor_sq_identity g)) × (hor_trans_id_right_sq (γ ·sqh α) = (hor_sq_identity h)).

Definition get_special_iso_squares {C: predoublecategory_sq_hor_data} {a b : C} (g: a -v-> b) (h: a -v-> b) 
  : UU 
  := ∑ (α : get_predoublecat_sq_special g h), (is_iso_square α).

Definition sqq_iso_special {C: predoublecategory_sq_hor_data} 
  {a b : C} (f: a -v-> b) (g: a -v-> b):  UU 
  := get_special_iso_squares f g. 

End Special_Iso_Squares.

Section Vertical_Composition_Squares.
(* We construct the vertical composition, noting it does not form a category *)

Definition predoublecategory_sq_ver_id_comp (C : predoublecategory_hor_sq): UU
    := 
      (∏ (a b : C) (f: a -h-> b), (sqq f (ver_identity a) (ver_identity b) f))  (* identities *)
        ×
      (∏ (a0 a1 b0 b1 c0 c1 : C) 
      (f0: a0 -h-> a1) (f1: b0 -h-> b1) (f2: c0 -h-> c1) (g0: a0 -v-> b0) (h0: b0 -v-> c0) (g1: a1 -v-> b1) (h1: b1 -v-> c1), 
        (sqq f0 g0 g1 f1) →
        (sqq f1 h0 h1 f2) →
        (sqq f0 (g0 ·v h0)  (g1 ·v h1) f2) (* composition *)
      ). 

Definition predoublecategory_sq_hor_ver_data : UU
      := ∑ C : predoublecategory_hor_sq, predoublecategory_sq_ver_id_comp C.
    
Definition make_predoublecategory_sq_hor_ver_data (C : predoublecategory_hor_sq)
        (id : (∏ (a b : C) (f: a -h-> b), (sqq f (ver_identity a) (ver_identity b) f)))
        (comp:  (∏ (a0 a1 b0 b1 c0 c1 : C) 
        (f0: a0 -h-> a1) (f1: b0 -h-> b1) (f2: c0 -h-> c1) (g0: a0 -v-> b0) (h0: b0 -v-> c0) (g1: a1 -v-> b1) (h1: b1 -v-> c1), 
          (sqq f0 g0 g1 f1) →
          (sqq f1 h0 h1 f2) →
          (sqq f0 (g0 ·v h0) (g1 ·v h1) f2)) )
      : predoublecategory_sq_hor_ver_data
      := tpair _ C (make_dirprod id comp).

Definition predoublecategory_hor_sq_from_predoublecategory_sq_hor_ver_data (C : predoublecategory_sq_hor_ver_data) :
  predoublecategory_hor_sq := pr1 C. (* Predoublegraph with vertical morphisms and squares composition *)
  
Coercion predoublecategory_hor_sq_from_predoublecategory_sq_hor_ver_data:
    predoublecategory_sq_hor_ver_data >-> predoublecategory_hor_sq.
    
    Definition get_ver_sq_identity {C : predoublecategory_sq_hor_ver_data}
      : (∏ (a b : C) (f: a -h-> b), (get_predoublecat_sq C a b a b f (ver_identity a) (ver_identity b) f))
      := pr1 (pr2 C).
    
    Definition ver_sq_identity {C : predoublecategory_sq_hor_ver_data} {a b : C} (f: a -h-> b):
      (get_predoublecat_sq C a b a b f (ver_identity a) (ver_identity b) f)
      := get_ver_sq_identity a b f.

    Definition ver_sq_compose {C : predoublecategory_sq_hor_ver_data} 
    { a0 a1 b0 b1 c0 c1 : C }
    {f0: a0 -h-> a1} {f1: b0 -h-> b1} {f2: c0 -h-> c1} {g0: a0 -v-> b0} {h0: b0 -v-> c0} {g1: a1 -v-> b1} {h1: b1 -v-> c1}
      : (sqq f0 g0 g1 f1) →
      (sqq f1 h0 h1 f2) →
      (sqq f0 (g0 ·v h0) (g1 ·v h1) f2) 
      := pr2 (pr2 C) a0 a1 b0 b1 c0 c1 f0 f1 f2 g0 h0 g1 h1.
  

Notation "α ·sqv β" := (ver_sq_compose α β) (at level 60).
Notation "α ∘sqv β" := (ver_sq_compose α β) (at level 60).

Section Vertical_Unitor_and_Associator_Coherences.
(* Define unitor and associator for the vertical composition*)

Definition ver_left_unitor { C:predoublecategory_sq_hor_ver_data} {a b: C}  (f: a -v-> b) : UU 
  := sqq_iso_special (ver_identity a ·v f) f.

Definition ver_right_unitor { C:predoublecategory_sq_hor_ver_data} {a b: C}  (f: a -v-> b) : UU 
    := sqq_iso_special (f ·v ver_identity b) f.

Definition ver_associator { C:predoublecategory_sq_hor_ver_data} {a b c d: C} 
(f : a -v-> b) (g : b -v-> c) (h : c -v-> d)
    := sqq_iso_special (f ·v (g ·v h)) ((f ·v g) ·v h).

Definition has_predoublecategory_sq_hor_ver_unit_assoc ( C:predoublecategory_sq_hor_ver_data) : UU 
:=     
 (∏ (a b: C) (f: a -v-> b) , sqq_iso_special (ver_identity a ·v f) f) × 
 (∏ (a b: C) (f: a -v-> b) , sqq_iso_special (f ·v ver_identity b) f) ×
 (∏ (a b c d: C) (f : a -v-> b) (g : b -v-> c) (h : c -v-> d), sqq_iso_special (f ·v (g ·v h)) ((f ·v g) ·v h)).

Definition predoublecategory_sq_hor_ver_unit_assoc_data : UU := 
  ∑ (C:predoublecategory_sq_hor_ver_data), has_predoublecategory_sq_hor_ver_unit_assoc C.

Coercion predoublecategory_sq_hor_ver_data_from_predoublecategory_sq_hor_ver_unit_assoc_data (C: predoublecategory_sq_hor_ver_unit_assoc_data) 
: predoublecategory_sq_hor_ver_data := pr1 C.

Definition get_ver_left_unitor {C: predoublecategory_sq_hor_ver_unit_assoc_data} {a b : C} (f: a -v-> b) : sqq_iso_special (ver_identity a ·v f) f
  := (pr12 C) a b f.

Definition get_ver_right_unitor {C: predoublecategory_sq_hor_ver_unit_assoc_data} {a b : C} (f: a -v-> b) : sqq_iso_special (f ·v ver_identity b) f
    := (pr122 C) a b f. 

Definition get_ver_associator {C: predoublecategory_sq_hor_ver_unit_assoc_data} {a b c d: C} 
    (f : a -v-> b) (g : b -v-> c) (h : c -v-> d) : sqq_iso_special (f ·v (g ·v h)) ((f ·v g) ·v h)
      := (pr222 C) a b c d f g h.

Definition predoublecategory_ver_left_unitor_naturality ( C : predoublecategory_sq_hor_ver_unit_assoc_data) : UU :=
  ∏ (a b c d : C)
  (f: a -h-> b) (g: a -v-> c) (h: b -v-> d) (k: c -h-> d)
  (α : sqq f g h k),
  (( hor_trans_id_right_sq ((( ver_sq_identity f) ·sqv α) ·sqh (pr1 (get_ver_left_unitor h)))) = ( hor_trans_id_left_sq ((pr1 (get_ver_left_unitor g)) ·sqh α))).
  
Definition predoublecategory_ver_right_unitor_naturality ( C : predoublecategory_sq_hor_ver_unit_assoc_data) : UU := 
  ∏ (a b c d : C)
  (f: a -h-> b) (g: a -v-> c) (h: b -v-> d) (k: c -h-> d)
  (α : sqq f g h k),
  (( hor_trans_id_right_sq ((α ·sqv (ver_sq_identity k)) ·sqh (pr1 (get_ver_right_unitor h)))) = ( hor_trans_id_left_sq ((pr1 (get_ver_right_unitor g)) ·sqh α))).

Definition predoublecategory_ver_assoc_naturality ( C : predoublecategory_sq_hor_ver_unit_assoc_data) : UU := 
  ∏ (a0 a1 a2 a3 b0 b1 b2 b3 : C)
  (fa: a0 -v-> a1) (fb: b0 -v-> b1) (ha: a1 -v-> a2) (hb: b1 -v-> b2) (ka: a2 -v-> a3) (kb: b2 -v-> b3)
  (g0: a0 -h-> b0) (g1: a1 -h-> b1) (g2: a2 -h-> b2) (g3: a3 -h-> b3)
  (α : sqq g0 fa fb g1) (β : sqq g1 ha hb g2) (γ : sqq g2 ka kb g3),
  (hor_trans_id_right_sq ( ( (α) ·sqv ( (β) ·sqv (γ)) ) ·sqh (pr1 (get_ver_associator fb hb kb)))) = 
  (hor_trans_id_left_sq ((pr1 (get_ver_associator fa ha ka)) ·sqh ( (α ·sqv β) ·sqv (γ) )) ).

Definition predoublecategory_ver_unitor_coherence ( C : predoublecategory_sq_hor_ver_unit_assoc_data) : UU :=
  ∏ (a b c: C)
  (f: a -v-> b) (g: b -v-> c),
    (hor_trans_id_right_sq ((pr1 (get_ver_associator f (ver_identity b) g)) ·sqh ( (pr1 (get_ver_right_unitor f)) ·sqv (hor_sq_identity g) ))  = 
    ((hor_sq_identity f) ·sqv (pr1 (get_ver_left_unitor g)))).

Definition predoublecategory_ver_assoc_coherence ( C : predoublecategory_sq_hor_ver_unit_assoc_data) : UU :=
  ∏  (a b c d e: C) (f : a -v-> b) (g : b -v-> c) (h : c -v-> d) (k : d -v-> e),
  (hor_trans_id_right_sq ( (pr1 (get_ver_associator f g (h ·v k))) ·sqh (pr1 (get_ver_associator (f ·v g) h k)) ))  = 
  (hor_trans_id_right_sq(hor_trans_id_right_sq ( ( ( (hor_sq_identity f) ·sqv (pr1 (get_ver_associator g h k)) ) 
  ·sqh (pr1 (get_ver_associator f (g ·v h) k)) ) 
  ·sqh  (  (pr1 (get_ver_associator f g h)) ·sqv (hor_sq_identity k)) ) )). 
  
Definition predoublecategory_interchange ( C : predoublecategory_sq_hor_ver_unit_assoc_data) : UU :=
  ∏ (a0 a1 a2 b0 b1 b2 c0 c1 c2 : C)
  (fa: a0 -h-> a1) (ga: a1 -h-> a2) (fb: b0 -h-> b1) (gb: b1 -h-> b2) (fc: c0 -h-> c1) (gc: c1 -h-> c2)
  (h0: a0 -v-> b0) (k0: b0 -v-> c0) (h1: a1 -v-> b1) (k1: b1 -v-> c1) (h2: a2 -v-> b2) (k2: b2 -v-> c2)
  (α : sqq fa h0 h1 fb)
  (β : sqq ga h1 h2 gb)
  (γ : sqq fb k0 k1 fc)
  (δ : sqq gb k1 k2 gc),
  (α ·sqh β) ·sqv (γ ·sqh δ) = (α ·sqv γ) ·sqh (β ·sqv δ).

End Vertical_Unitor_and_Associator_Coherences.

Notation "α ·sqv β" := (ver_sq_compose α β) (at level 60).
Notation "α ∘sqv β" := (ver_sq_compose α β) (at level 60).
  
Section Pre_Double_Categories. (*Finally we define double categories by adding appropriate set truncation conditions. *)
     
Definition has_sq_hor_homsets (C : predoublecategory_hor_sq) : UU := 
  ∏ (a b c d : C) (g: a -v-> c) (h: b -v-> d), isaset (hom_sq_between_ver C g h).

  Definition doublecategory_hor_sq := ∑ C:predoublecategory_hor_sq, has_sq_hor_homsets C.
  
  Definition make_doublecategory_hor_sq C h : doublecategory_hor_sq := C,,h.
  
  Definition doublecategory_hor_sq_to_predoublecategory_hor_sq : doublecategory_hor_sq -> predoublecategory_hor_sq := pr1.


  Definition predoublecategory : UU := 
    ∑ (C:predoublecategory_sq_hor_ver_unit_assoc_data), 
    ( (predoublecategory_ver_left_unitor_naturality C) ×
    (predoublecategory_ver_right_unitor_naturality C) ×
    (predoublecategory_ver_assoc_naturality C) ×
    (predoublecategory_ver_unitor_coherence C) ×
    (predoublecategory_ver_assoc_coherence C) ×
    (predoublecategory_interchange C)) .

Coercion predoublecategory_sq_hor_ver_unit_assoc_data_from_predoublecategory (C: predoublecategory) 
    : predoublecategory_sq_hor_ver_unit_assoc_data := pr1 C.

End Pre_Double_Categories.

Section Underlying_Category_Vertical_Morphisms_Squares. 
(* We now show the horizontal composition of squares gives us a category. *)

Definition und_ver_cat_ob (C: predoublecategory_hor_sq) : UU := 
    ∑ (a b : C), a -v-> b. 
     
Definition get_und_ver_cat_ob {C: predoublecategory_hor_sq} {a b : C} (f: a -v-> b) : und_ver_cat_ob C 
    :=  (a,, (b,, f)).  

Definition get_und_ver_cat_ob_mor {C: predoublecategory_hor_sq} (c d : und_ver_cat_ob C) : UU := 
      ∑ (g: (pr1 c) -h-> (pr1 d)) (k: (pr12 c) -h-> (pr12 d)), (sqq g (pr22 c) (pr22 d) k ).
  
Definition und_ver_cat_ob_mor (C: predoublecategory_hor_sq) : und_ver_cat_ob C → und_ver_cat_ob C → UU :=
      fun c d => (get_und_ver_cat_ob_mor c d).  

Definition make_und_ver_cat_ob_mor {C: predoublecategory_hor_sq} 
      {c d : und_ver_cat_ob C} {g: (pr1 c) -h-> (pr1 d)} {k: (pr12 c) -h-> (pr12 d)} 
        (α : sqq g (pr22 c) (pr22 d) k )  : und_ver_cat_ob_mor C c d
      := (g ,, (k ,, α)).

Definition has_hor_sq_homsets (C : predoublecategory_hor_sq) : UU := 
  ∏ (a b c d: C)
  (f: a -v-> b) (g: c -v-> d),
  isaset (und_ver_cat_ob_mor C (get_und_ver_cat_ob f) (get_und_ver_cat_ob g)). (*Horizontal Square Hom sets *)

Definition get_und_ver_cat_id {C: predoublecategory_hor_sq} (c : (und_ver_cat_ob C)) : und_ver_cat_ob_mor C c c
:=  make_und_ver_cat_ob_mor (hor_sq_identity (pr22 c)).

Definition und_ver_cat_id (C: predoublecategory_hor_sq) : ∏ c : und_ver_cat_ob C, und_ver_cat_ob_mor C c c :=  
fun c => get_und_ver_cat_id c.

Definition get_und_ver_cat_comp {C: predoublecategory_hor_sq} (c d e : (und_ver_cat_ob C)) : 
und_ver_cat_ob_mor C c d → und_ver_cat_ob_mor C d e → und_ver_cat_ob_mor C c e
:= fun α β => make_und_ver_cat_ob_mor ( (pr22 α) ·sqh (pr22 β)).

Definition und_ver_cat_comp (C: predoublecategory_hor_sq) : 
∏ c d e: und_ver_cat_ob C, und_ver_cat_ob_mor C c d → und_ver_cat_ob_mor C d e → und_ver_cat_ob_mor C c e :=  
fun c d e => get_und_ver_cat_comp c d e.

Definition make_und_ver_cat_comp {C: predoublecategory_hor_sq} {c d e : (und_ver_cat_ob C)}
(f: und_ver_cat_ob_mor C c d) (g: und_ver_cat_ob_mor C d e) : und_ver_cat_ob_mor C c e := und_ver_cat_comp C c d e f g.

Definition und_ver_cat_precategory_data (C: predoublecategory_hor_sq) : precategory_data :=
  make_precategory_data (make_precategory_ob_mor (und_ver_cat_ob C) (und_ver_cat_ob_mor C)) (und_ver_cat_id C) (und_ver_cat_comp C).

Lemma und_ver_cat_morphism_eq_principle {C: predoublecategory_hor_sq} {c d : und_ver_cat_ob C} (f g : und_ver_cat_ob_mor C c d) 
(equp: (pr1 f) = (pr1 g)) (eqdown: (pr12 f) = (pr12 g)) 
(eqmid: boundary_sq_transport (equp) (idpath (pr22 c)) (idpath (pr22 d)) (eqdown) (pr22 f) = (pr22 g) ) : f = g.
Proof.
  induction f as [ f1 [ f2 sq1 ]].
  induction g as [ g1 [ g2 sq2 ]].
  cbn in *.
  induction equp.
  induction eqdown.
  apply maponpaths.
  apply maponpaths.
  induction eqmid.
  exact (idpath sq1).
Defined.

Definition und_ver_left_unit 
  {C: predoublecategory_hor_sq} 
  {c d : und_ver_cat_ob C} 
  (f: get_und_ver_cat_ob_mor c d) : (make_und_ver_cat_comp (und_ver_cat_id C c) f) = f
  := (und_ver_cat_morphism_eq_principle 
  (make_und_ver_cat_comp (und_ver_cat_id C c) f) f (id_hor_left (pr1 f)) (id_hor_left (pr12 f)) (id_hor_sq_left (pr22 f))).

Definition get_und_ver_left_unit (C: predoublecategory_hor_sq) : 
∏ (c d : und_ver_cat_precategory_data C) (f: get_und_ver_cat_ob_mor c d), 
(make_und_ver_cat_comp (und_ver_cat_id C c) f) = f
:= fun c d f => und_ver_left_unit f.

Definition und_ver_right_unit 
  {C: predoublecategory_hor_sq} 
  {c d : und_ver_cat_ob C} 
  (f: get_und_ver_cat_ob_mor c d) : (make_und_ver_cat_comp f (und_ver_cat_id C d)) = f
  := (und_ver_cat_morphism_eq_principle 
  (make_und_ver_cat_comp f (und_ver_cat_id C d)) f (id_hor_right (pr1 f)) (id_hor_right (pr12 f)) (id_hor_sq_right (pr22 f))).

  Definition get_und_ver_right_unit (C: predoublecategory_hor_sq) : ∏ (c d : und_ver_cat_ob C) (f: get_und_ver_cat_ob_mor c d), 
  (make_und_ver_cat_comp f (und_ver_cat_id C d)) = f
  := fun c d f => und_ver_right_unit f.

Definition und_ver_assoc
  {C: predoublecategory_hor_sq} 
  {a b c d : und_ver_cat_ob C}
  (f: get_und_ver_cat_ob_mor a b) (g: get_und_ver_cat_ob_mor b c) (h: get_und_ver_cat_ob_mor c d) : 
  make_und_ver_cat_comp f (make_und_ver_cat_comp g h) = make_und_ver_cat_comp (make_und_ver_cat_comp f g) h 
  := (und_ver_cat_morphism_eq_principle 
  (make_und_ver_cat_comp f (make_und_ver_cat_comp g h)) (make_und_ver_cat_comp (make_und_ver_cat_comp f g) h) 
  (assoc_hor (pr1 f) (pr1 g) (pr1 h)) (assoc_hor (pr12 f) (pr12 g) (pr12 h)) (assoc_sq_hor (pr22 f) (pr22 g) (pr22 h))).

Definition get_und_ver_assoc (C: predoublecategory_hor_sq) : 
∏ (a b c d : und_ver_cat_ob C) (f: get_und_ver_cat_ob_mor a b) (g: get_und_ver_cat_ob_mor b c) (h: get_und_ver_cat_ob_mor c d),
make_und_ver_cat_comp f (make_und_ver_cat_comp g h) = make_und_ver_cat_comp (make_und_ver_cat_comp f g) h
:= fun a b c d f g h => und_ver_assoc f g h.


Definition und_ver_cat_is_precategory (C: predoublecategory_hor_sq) : is_precategory (und_ver_cat_precategory_data C) 
  := make_is_precategory_one_assoc (get_und_ver_left_unit C) (get_und_ver_right_unit C) (get_und_ver_assoc C).
  

Definition und_ver_precategory (C: predoublecategory_hor_sq) : precategory := 
  make_precategory (und_ver_cat_precategory_data C) (und_ver_cat_is_precategory C).

End Underlying_Category_Vertical_Morphisms_Squares.

Section Double_Categories. (* We now use the underlying categories to define double categories *)

Definition doublecategory := ∑ C:predoublecategory, (has_homsets (und_ob_hor_precategory C) × has_homsets (und_ver_precategory C)).
        
Definition make_doublecategory C h k : doublecategory := C,,h,,k.
        
Definition doublecategory_to_predoublecategory : doublecategory → predoublecategory := pr1.
        
Coercion doublecategory_to_predoublecategory : doublecategory >-> predoublecategory.
        
Coercion homset_sq_property (C : doublecategory) : (has_homsets (und_ob_hor_precategory C) × has_homsets (und_ver_precategory C)) := pr2 C.
  
Definition und_ob_hor_cat (C: doublecategory) : category := make_category (und_ob_hor_precategory C) (pr12 C).

Definition und_ver_cat (C: doublecategory) : category := make_category (und_ver_precategory C) (pr22 C).

End Double_Categories.

Section Univalent_Double_Categories.
(* We now use the underlying categories to define double univalence, as the univalence of the underlying two categories *)

Definition is_double_univalent (C: doublecategory) := (is_univalent (und_ob_hor_cat C) × is_univalent (und_ver_cat C)).

Definition univalent_doublecategory : UU := ∑ (C: doublecategory), is_double_univalent C.

Coercion univalent_doublecategory_to_doublecategory (C: univalent_doublecategory) := pr1 C. 

End Univalent_Double_Categories.
