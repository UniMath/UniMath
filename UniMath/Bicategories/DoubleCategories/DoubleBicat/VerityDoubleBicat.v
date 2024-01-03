(*****************************************************************************************

 Verity double bicategories

 In this file, we define the notion of double bicategory as given in Verity's PhD thesis.

 There are numerous examples of pseudo double categories. For example, every category `C`
 with pullbacks gives rise to a double category whose vertical morphisms are given by
 morphisms in `C` and whose horizontal morphisms are given by spans in `C`. Another example
 is given by the category of sets where the horizontal morphisms are given by relations in
 sets. However, univalent categories with functors and profunctors does not form a pseudo
 double category. The reason for that is as follows: in a pseudo double category, the
 vertical morphisms must form a set. However, the types of functors between univalent
 categories is not necessarily a set, as that would imply that there is a unique natural
 isomorphism between any two functors. This is similar to the fact that we do not have a
 category of univalent categories, but only a bicategory of univalent categories.

 For that reason, we need a more flexible notion of double category that encompasses
 examples such as univalent categories with functors and profunctors, univalent enriched
 categories with functors and profunctors, and the quintet construction on a bicategory
 (i.e., the double category whose horizontal and vertical morphisms are given by 1-cells
 and whose squares are given by 2-cells of the apropriate type). The notion that we use
 for that purpose is that of a double bicategory as defined by Verity.

 Double bicategories are like pseudo double categories, but there is one crucial difference.
 In a pseudo double category, composition is weakly associative and unital in one direction,
 but in the other direction, it is strictly associative and unital. For a double bicategory,
 composition is weakly associative and unital in both directions. There is yet another
 difference: due to the strictness in pseudo double categories, one needs to use transports
 to formulate some of the laws. However, for double bicategories no transports are needed to
 formulate any of the laws.

 The notion of double bicategory is rather complicated and it consists of many fields. For
 this reason, we use numerous intermediate definitions in our definition of a double
 bicategory.

 To define double bicategories, we take several steps. We start with the following:
 - We define bicategories together with horizontal morphisms and squares ([hor_sq_bicat]).
   These are defined to be a pair of a bicategory together with the data of a 2-sided
   displayed category on it. Note that we also have vertical identity squares and vertical
   composition of squares.
 - We add the data and laws necessary to obtain a bicategory of objects and horizontal
   morphisms ([hor_bicat_sq_bicat]). To do so, we reuse the definitions that are used to
   define bicategories.
 - We add horizontal identity squares and horizontal composition of squares
   ([hor_bicat_sq_bicat_hor_id_comp]).
 - We add whiskering operations on squares ([double_bicat_whiskering]). The notation for
   whiskering is based on the notation for whiskering in bicategories. The difference is
   that we have 4 whiskering operations for double bicategories, because squares have 4
   sides. The convention that we use, is that the 2-cell is always on the left and the
   square is always on the right. The symbol is one of `◃s, ▹s, ▵s, ▿s`, and it indicates
   the relative placement of the 2-cell compared to the square. More specifically, `τ ◃s s`
   means that we whisker a 2-cell on the left side of a square, `τ ▹s s` means that we
   whisker a 2-cell on the right side of a square, `τ ▵s s` means that we whisker a 2-cell
   on the top side of a square, and `τ ▿s s` means that we whisker a 2-cell on the bottom
   side of a square.

 At this point, we have the data in Definition 1.4.1 in Verity, and also the laws described
 in items (iv) and (v). As such, with these definitions we have all the data necessary to
 define double bicategories. Next we add all laws for double bicategories. Instead of
 writing down all laws in a single definition, we again split it up into several definitions,
 because that makes it easier to keep oversight. First of all, we have laws about the
 whiskering operations for double bicategories.
 - We have identity and composition laws for whiskering. These are split in four definitions:
   one for left whiskering ([lwhisker_square_id_comp_law]), one for right whiskering
   ([rwhisker_square_id_comp_law]), one for up whiskering ([uwhisker_square_id_comp_law]),
   and one for down whiskering ([dwhisker_square_id_comp_law]).
 - We have compatibility laws for whiskering ([whisker_square_compatible]).
 - We have laws for whiskering an identity squares ([whisker_square_id_square]).
 - We have laws for whiskering and composition ([whisker_square_comp_square]).

 It is good to be aware of the sheer complexity of this definition.
 - The data of a bicategory ([prebicat_data]) consists of 15 fields.
 - There are 22 laws for bicategories ([prebicat_laws] and [isaset_cells]).

 As such, having two bicategories already gives rise to 74 fields. Since the two bicategories
 in the definition of a double bicategory share their type of objects, this already gives
 a definition with 73 fields. But a double bicategory consists of more.
 - We have 4 whiskering operations. Each whiskering operation comes with 2 laws, and
   there are 6 compatibility laws regarding whiskering. This contains 18 fields
 - We have a type of squares. We have two identity squares and two composition operations
   on squares. This contains 4 fields of data.
 - There are 6 compatibility laws that guide the interaction between vertical composition
   of squares and whiskering, and the same for the horizontal case. This gives 12 fields.
 - There is one compatibility law that guide the interaction between vertical identity
   squares and whiskering, and the same for the horizontal case. From this, we get 2 fields.

 This means that we already have 109 fields in our definition of double bicategory. But
 there is still more to what constitutes a double bicategory.
 - We have the interchange law (1 field).
 - We have 3 laws about vertical/horizontal identity squares. (3 fields).

 At this point, we already have 112 fields in our definition of double bicategory, and yet,
 we still need to several laws, namely those about cylinders. Cylinders come in two
 variations, namely horizontal ([is_hor_cylinder]) and vertical ones ([is_verr_cylinder]).
 There are several laws about cylinders.
 - The interaction of horizontal/vertical composition of squares with cylinders. This
   gives rise to 2 laws.
 - The associator is a horizontal and a vertical cylinder. This gives 2 laws.
 - The left and right unitors are horizontal and vertical cylinders. This gives 4 laws.
 - We also need to require that the squares form a set.
 In total, we thus have 121 fields in our definition of double bicategory. Each of these
 fields corresponds to something in Verity's definition of a double bicategory. Note that
 even though a fully unfolded definition that doesn't reuse anything is possible, such a
 definition would be extremely tedious to write down, while the resulting definition would
 not have any advantage compared to the definition in this file.

 Note that the name double bicategory might be confusing. This is due to the following
 systematic in the terminology of double categories.
 - A strict double category is a category internal to the category of categories.
 - A pseudo double category is a pseudocategory internal to the bicategory of categories.
 However, such terminology falls apart for Verity double bicategories, as they are not
 defined to be bicategories internal to the tricategory of bicategories. The latter
 notion has been considered by Morton, who showed that Verity double bicategories are a
 special case of internal bicategories.

 Finally, we define a special case of Verity double bicategories, namely those for which
 the horizontal and vertical 2-cells correspond to a certain class of squares.

 References
 - Enriched Categories, Internal Categories and Change of Base
   Dominic Verity
   ([http://www.tac.mta.ca/tac/reprints/articles/20/tr20.pdf])
 - Double bicategories and double cospans
   Jeffrey C. Morton
   ([https://arxiv.org/abs/math/0611930])

 Contents
 1. Bicategories with squares
 2. Horizontal and vertical bicategory with squares
 3. Horizontal identity squares and horizontal composition of squares
 4. Whiskering operations
 5. Identity and composition laws for whiskering (items (i)-(v) in Verity)
 6. Laws relating composition and identity squares (items (ix) and (x) in Verity)
 7. Laws about cylinders (items (vi)-(vii) in Verity)
 8. Verity double bicategories
 9. Unfolded versions of the laws for Verity double bicategories

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.

Local Open Scope cat.

Declare Scope double_bicat.

Local Open Scope double_bicat.

(** * 1. Bicategories with squares *)
Definition ver_sq_bicat
  : UU
  := ∑ (B : bicat), twosided_disp_cat_data B B.

Definition make_ver_sq_bicat
           (B : bicat)
           (D : twosided_disp_cat_data B B)
  : ver_sq_bicat
  := B ,, D.

Coercion ver_bicat_of_ver_sq_bicat
         (B : ver_sq_bicat)
  : bicat
  := pr1 B.

Definition twosided_disp_cat_data_of_ver_sq_bicat
           (B : ver_sq_bicat)
  : twosided_disp_cat_data B B
  := pr2 B.

Definition ver_mor_ver_sq_bicat
           {B : ver_sq_bicat}
           (x y : B)
  : UU
  := twosided_disp_cat_data_of_ver_sq_bicat B x y.

(** * 2. Horizontal and vertical bicategory with squares *)
Definition precat_ob_ver_mor
           (B : ver_sq_bicat)
  : precategory_ob_mor
  := make_precategory_ob_mor (ob B) (λ x y, ver_mor_ver_sq_bicat x y).

Definition ver_sq_bicat_ver_id_comp
           (B : ver_sq_bicat)
  : UU
  := precategory_id_comp (precat_ob_ver_mor B)
     ×
     prebicat_2cell_struct (precat_ob_ver_mor B).

Definition prebicat_1_id_comp_cells_ver_id_comp_cells
           {B : ver_sq_bicat}
           (I : ver_sq_bicat_ver_id_comp B)
  : prebicat_1_id_comp_cells
  := (precat_ob_ver_mor B ,, pr1 I) ,, pr2 I.

Definition ver_sq_bicat_id_comp_cells
           {B : ver_sq_bicat}
           (I : ver_sq_bicat_ver_id_comp B)
  : UU
  := prebicat_2_id_comp_struct (prebicat_1_id_comp_cells_ver_id_comp_cells I).

Definition prebicat_data_ver_id_comp_cells
           {B : ver_sq_bicat}
           {I : ver_sq_bicat_ver_id_comp B}
           (J : ver_sq_bicat_id_comp_cells I)
  : prebicat_data
  := prebicat_1_id_comp_cells_ver_id_comp_cells I ,, J.

Definition ver_sq_bicat_prebicat_laws
           {B : ver_sq_bicat}
           {I : ver_sq_bicat_ver_id_comp B}
           (J : ver_sq_bicat_id_comp_cells I)
  : UU
  := prebicat_laws (prebicat_data_ver_id_comp_cells J).

Definition prebicat_ver_sq_bicat_prebicat_laws
           {B : ver_sq_bicat}
           {I : ver_sq_bicat_ver_id_comp B}
           {J : ver_sq_bicat_id_comp_cells I}
           (H : ver_sq_bicat_prebicat_laws J)
  : prebicat
  := prebicat_data_ver_id_comp_cells J ,, H.

Definition ver_bicat_sq_bicat
  : UU
  := ∑ (B : ver_sq_bicat)
       (I : ver_sq_bicat_ver_id_comp B)
       (J : ver_sq_bicat_id_comp_cells I)
       (H : ver_sq_bicat_prebicat_laws J),
     isaset_cells (prebicat_ver_sq_bicat_prebicat_laws H).

Definition make_ver_bicat_sq_bicat
           (B : ver_sq_bicat)
           (I : ver_sq_bicat_ver_id_comp B)
           (J : ver_sq_bicat_id_comp_cells I)
           (H : ver_sq_bicat_prebicat_laws J)
           (K : isaset_cells (prebicat_ver_sq_bicat_prebicat_laws H))
  : ver_bicat_sq_bicat
  := B ,, I ,, J ,, H ,, K.

Coercion ver_bicat_to_ver_bicat
         (B : ver_bicat_sq_bicat)
  : ver_sq_bicat
  := pr1 B.

Definition ver_bicat_of_ver_bicat_sq_bicat
           (B : ver_bicat_sq_bicat)
  : bicat.
Proof.
  simple refine (_ ,, _).
  - exact (prebicat_ver_sq_bicat_prebicat_laws (pr1 (pr222 B))).
  - exact (pr2 (pr222 B)).
Defined.

Notation "x -|-> y" := (ver_bicat_of_ver_bicat_sq_bicat _ ⟦ x , y ⟧) (at level 55)
  : double_bicat.
Notation "h =|=> k" := ((h : ver_bicat_of_ver_bicat_sq_bicat _ ⟦ _ , _ ⟧) ==> k ) (at level 60)
  : double_bicat.

Definition square_double_bicat
           {B : ver_bicat_sq_bicat}
           {w x y z : B}
           (h₁ : w --> x)
           (h₂ : y --> z)
           (v₁ : w -|-> y)
           (v₂ : x -|-> z)
  : UU
  := v₁ -->[ h₁ ][ h₂ ] v₂.

Notation "'id_h'" := identity.
Notation "'id_v'" := (identity (C := ver_bicat_of_ver_bicat_sq_bicat _)).

(** * 3. Horizontal identity squares and verizontal composition of squares *)
Definition ver_bicat_sq_bicat_to_ver_twosided_disp_cat_ob_mor
           (B : ver_bicat_sq_bicat)
  : twosided_disp_cat_ob_mor
      (ver_bicat_of_ver_bicat_sq_bicat B)
      (ver_bicat_of_ver_bicat_sq_bicat B).
Proof.
  simple refine (_ ,, _).
  - exact (λ (x y : B), x --> y).
  - exact (λ w x y z h₁ h₂ v₁ v₂, square_double_bicat h₁ h₂ v₁ v₂).
Defined.

Definition ver_bicat_sq_bicat_ver_id_comp_sq
           (B : ver_bicat_sq_bicat)
  : UU
  := twosided_disp_cat_id_comp
       (ver_bicat_sq_bicat_to_ver_twosided_disp_cat_ob_mor B).

Definition ver_bicat_sq_bicat_ver_id_comp
  : UU
  := ∑ (B : ver_bicat_sq_bicat),
     ver_bicat_sq_bicat_ver_id_comp_sq B.

Coercion ver_bicat_sq_bicat_ver_id_comp_to_ver_bicat_sq_bicat
         (B : ver_bicat_sq_bicat_ver_id_comp)
  : ver_bicat_sq_bicat
  := pr1 B.

Definition make_ver_bicat_sq_bicat_ver_id_comp
           (B : ver_bicat_sq_bicat)
           (I : ver_bicat_sq_bicat_ver_id_comp_sq B)
  : ver_bicat_sq_bicat_ver_id_comp
  := B ,, I.

Definition id_h_square_bicat
           {B : ver_bicat_sq_bicat_ver_id_comp}
           {x y : B}
           (v : x -|-> y)
  : square_double_bicat (id_h x) (id_h y) v v
  := pr12 (pr211 B) x y v.

Definition comp_h_square_bicat
           {B : ver_bicat_sq_bicat_ver_id_comp}
           {x₁ x₂ x₃ y₁ y₂ y₃ : B}
           {h₁ : x₁ --> x₂}
           {h₂ : x₂ --> x₃}
           {k₁ : y₁ --> y₂}
           {k₂ : y₂ --> y₃}
           {v₁ : x₁ -|-> y₁}
           {v₂ : x₂ -|-> y₂}
           {v₃ : x₃ -|-> y₃}
           (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
           (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
  : square_double_bicat (h₁ · h₂) (k₁ · k₂) v₁ v₃
  := pr22 (pr211 B) x₁ x₂ x₃ y₁ y₂ y₃ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂.

Notation "s₁ ⋆h s₂" := (comp_h_square_bicat s₁ s₂) (at level 37, left associativity)
  : double_bicat.

Definition id_v_square_bicat
           {B : ver_bicat_sq_bicat_ver_id_comp}
           {x y : B}
           (h : x --> y)
  : square_double_bicat h h (id_v x) (id_v y)
  := pr12 B x y h.

Definition comp_v_square_bicat
           {B : ver_bicat_sq_bicat_ver_id_comp}
           {x₁ x₂ y₁ y₂ z₁ z₂ : B}
           {h₁ : x₁ --> x₂}
           {h₂ : y₁ --> y₂}
           {h₃ : z₁ --> z₂}
           {v₁ : x₁ -|-> y₁}
           {v₂ : y₁ -|-> z₁}
           {w₁ : x₂ -|-> y₂}
           {w₂ : y₂ -|-> z₂}
           (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
           (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
  : square_double_bicat h₁ h₃ (v₁ · v₂) (w₁ · w₂)
  := pr22 B x₁ y₁ z₁ x₂ y₂ z₂ h₁ h₂ h₃ v₁ v₂ w₁ w₂ s₁ s₂.

Notation "s₁ ⋆v s₂" := (comp_v_square_bicat s₁ s₂) (at level 40, left associativity)
  : double_bicat.

(** * 4. Whiskering operations *)
Definition double_bicat_whiskering
           (B : ver_bicat_sq_bicat_ver_id_comp)
  : UU
  := (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ v₁' : w -|-> y)
        (v₂ : x -|-> z)
        (τ : v₁ =|=> v₁'),
      square_double_bicat h₁ h₂ v₁' v₂
      →
      square_double_bicat h₁ h₂ v₁ v₂)
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ v₂' : x -|-> z)
        (τ : v₂ =|=> v₂'),
      square_double_bicat h₁ h₂ v₁ v₂
      →
      square_double_bicat h₁ h₂ v₁ v₂')
     ×
     (∏ (w x y z : B)
        (h₁ h₁' : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (τ : h₁ ==> h₁'),
      square_double_bicat h₁' h₂ v₁ v₂
      →
      square_double_bicat h₁ h₂ v₁ v₂)
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ h₂' : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (τ : h₂ ==> h₂'),
      square_double_bicat h₁ h₂ v₁ v₂
      →
      square_double_bicat h₁ h₂' v₁ v₂).

Definition ver_bicat_sq_id_comp_whisker
  : UU
  := ∑ (B : ver_bicat_sq_bicat_ver_id_comp),
     double_bicat_whiskering B.

Definition make_ver_bicat_sq_id_comp_whisker
           (B : ver_bicat_sq_bicat_ver_id_comp)
           (W : double_bicat_whiskering B)
  : ver_bicat_sq_id_comp_whisker
  := B ,, W.

Coercion ver_bicat_sq_id_comp_whisker_to_ver_bicat_sq_bicat_ver_id_comp
         (B : ver_bicat_sq_id_comp_whisker)
  : ver_bicat_sq_bicat_ver_id_comp
  := pr1 B.

Definition lwhisker_square
           {B : ver_bicat_sq_id_comp_whisker}
           {w x y z : B}
           {h₁ : w --> x}
           {h₂ : y --> z}
           {v₁ v₁' : w -|-> y}
           {v₂ : x -|-> z}
           (τ : v₁ =|=> v₁')
           (s : square_double_bicat h₁ h₂ v₁' v₂)
  : square_double_bicat h₁ h₂ v₁ v₂
  := pr1 (pr2 B) w x y z h₁ h₂ v₁ v₁' v₂ τ s.

Notation "τ ◃s s" := (lwhisker_square τ s) (at level 60) : double_bicat.

Definition rwhisker_square
           {B : ver_bicat_sq_id_comp_whisker}
           {w x y z : B}
           {h₁ : w --> x}
           {h₂ : y --> z}
           {v₁ : w -|-> y}
           {v₂ v₂' : x -|-> z}
           (τ : v₂ =|=> v₂')
           (s : square_double_bicat h₁ h₂ v₁ v₂)
  : square_double_bicat h₁ h₂ v₁ v₂'
  := pr12 (pr2 B) w x y z h₁ h₂ v₁ v₂ v₂' τ s.

Notation "τ ▹s s" := (rwhisker_square τ s) (at level 60) : double_bicat.

Definition uwhisker_square
           {B : ver_bicat_sq_id_comp_whisker}
           {w x y z : B}
           {h₁ h₁' : w --> x}
           {h₂ : y --> z}
           {v₁ : w -|-> y}
           {v₂ : x -|-> z}
           (τ : h₁ ==> h₁')
           (s : square_double_bicat h₁' h₂ v₁ v₂)
  : square_double_bicat h₁ h₂ v₁ v₂
  := pr122 (pr2 B) w x y z h₁ h₁' h₂ v₁ v₂ τ s.

Notation "τ ▵s s" := (uwhisker_square τ s) (at level 60) : double_bicat.

Definition dwhisker_square
           {B : ver_bicat_sq_id_comp_whisker}
           {w x y z : B}
           {h₁ : w --> x}
           {h₂ h₂' : y --> z}
           {v₁ : w -|-> y}
           {v₂ : x -|-> z}
           (τ : h₂ ==> h₂')
           (s : square_double_bicat h₁ h₂ v₁ v₂)
  : square_double_bicat h₁ h₂' v₁ v₂
  := pr222 (pr2 B) w x y z h₁ h₂ h₂' v₁ v₂ τ s.

Notation "τ ▿s s" := (dwhisker_square τ s) (at level 60) : double_bicat.

(** * 5. Identity and composition laws for whiskering (items (i)-(v) in Verity) *)
Definition lwhisker_square_id_comp_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      id2 v₁ ◃s s = s)
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ v₁' v₁'' : w -|-> y)
        (v₂ : x -|-> z)
        (τ₁ : v₁ =|=> v₁')
        (τ₂ : v₁' =|=> v₁'')
        (s : square_double_bicat h₁ h₂ v₁'' v₂),
      (τ₁ • τ₂) ◃s s = τ₁ ◃s (τ₂ ◃s s)).

Definition rwhisker_square_id_comp_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      id2 v₂ ▹s s = s)
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ v₂' v₂'' : x -|-> z)
        (τ₁ : v₂ =|=> v₂')
        (τ₂ : v₂' =|=> v₂'')
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      (τ₁ • τ₂) ▹s s = τ₂ ▹s (τ₁ ▹s s)).

Definition uwhisker_square_id_comp_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      id2 h₁ ▵s s = s)
     ×
     (∏ (w x y z : B)
        (h₁ h₁' h₁'' : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (τ₁ : h₁ ==> h₁')
        (τ₂ : h₁' ==> h₁'')
        (s : square_double_bicat h₁'' h₂ v₁ v₂),
      (τ₁ • τ₂) ▵s s = τ₁ ▵s (τ₂ ▵s s)).

Definition dwhisker_square_id_comp_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      id2 h₂ ▿s s = s)
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ h₂' h₂'' : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (τ₁ : h₂ ==> h₂')
        (τ₂ : h₂' ==> h₂'')
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      (τ₁ • τ₂) ▿s s = τ₂ ▿s (τ₁ ▿s s)).

Definition whisker_square_compatible
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (w x y z : B)
        (h₁ h₁' : w --> x)
        (h₂ h₂' : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (τ : h₁ ==> h₁')
        (θ : h₂ ==> h₂')
        (s : square_double_bicat h₁' h₂ v₁ v₂),
      θ ▿s (τ ▵s s) = τ ▵s (θ ▿s s))
     ×
     (∏ (w x y z : B)
        (h₁ h₁' : w --> x)
        (h₂ : y --> z)
        (v₁ v₁' : w -|-> y)
        (v₂ : x -|-> z)
        (τ : h₁ ==> h₁')
        (θ : v₁ ==> v₁')
        (s : square_double_bicat h₁' h₂ v₁' v₂),
      θ ◃s (τ ▵s s) = τ ▵s (θ ◃s s))
     ×
     (∏ (w x y z : B)
        (h₁ h₁' : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ v₂' : x -|-> z)
        (τ : h₁ ==> h₁')
        (θ : v₂ ==> v₂')
        (s : square_double_bicat h₁' h₂ v₁ v₂),
      θ ▹s (τ ▵s s) = τ ▵s (θ ▹s s))
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ h₂' : y --> z)
        (v₁ v₁' : w -|-> y)
        (v₂ : x -|-> z)
        (τ : h₂ ==> h₂')
        (θ : v₁ =|=> v₁')
        (s : square_double_bicat h₁ h₂ v₁' v₂),
      θ ◃s (τ ▿s s) = τ ▿s (θ ◃s s))
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ h₂' : y --> z)
        (v₁ : w -|-> y)
        (v₂ v₂' : x -|-> z)
        (τ : h₂ ==> h₂')
        (θ : v₂ =|=> v₂')
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      θ ▹s (τ ▿s s) = τ ▿s (θ ▹s s))
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ v₁' : w -|-> y)
        (v₂ v₂' : x -|-> z)
        (τ : v₁ =|=> v₁')
        (θ : v₂ =|=> v₂')
        (s : square_double_bicat h₁ h₂ v₁' v₂),
      θ ▹s (τ ◃s s) = τ ◃s (θ ▹s s)).

Definition whisker_square_id_square
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (x y : B)
        (v w : x -|-> y)
        (τ : v =|=> w),
      τ ◃s id_h_square_bicat w = τ ▹s id_h_square_bicat v)
     ×
     (∏ (x y : B)
        (h k : x --> y)
        (τ : h ==> k),
      τ ▵s id_v_square_bicat k = τ ▿s id_v_square_bicat h).

Definition whisker_square_comp_square
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (x₁ x₂ y₁ y₂ z₁ z₂ : B)
        (h₁ h₁' : x₁ --> x₂)
        (h₂ : y₁ --> y₂)
        (h₃ : z₁ --> z₂)
        (v₁ : x₁ -|-> y₁)
        (v₂ : y₁ -|-> z₁)
        (w₁ : x₂ -|-> y₂)
        (w₂ : y₂ -|-> z₂)
        (τ : h₁ ==> h₁')
        (s₁ : square_double_bicat h₁' h₂ v₁ w₁)
        (s₂ : square_double_bicat h₂ h₃ v₂ w₂),
      τ ▵s (s₁ ⋆v s₂) = (τ ▵s s₁) ⋆v s₂)
     ×
     (∏ (x₁ x₂ y₁ y₂ z₁ z₂ : B)
        (h₁ : x₁ --> x₂)
        (h₂ : y₁ --> y₂)
        (h₃ h₃' : z₁ --> z₂)
        (v₁ : x₁ -|-> y₁)
        (v₂ : y₁ -|-> z₁)
        (w₁ : x₂ -|-> y₂)
        (w₂ : y₂ -|-> z₂)
        (τ : h₃ ==> h₃')
        (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
        (s₂ : square_double_bicat h₂ h₃ v₂ w₂),
      τ ▿s (s₁ ⋆v s₂) = s₁ ⋆v (τ ▿s s₂))
     ×
     (∏ (x₁ x₂ y₁ y₂ z₁ z₂ : B)
        (h₁ : x₁ --> x₂)
        (h₂ h₂' : y₁ --> y₂)
        (h₃ : z₁ --> z₂)
        (v₁ : x₁ -|-> y₁)
        (v₂ : y₁ -|-> z₁)
        (w₁ : x₂ -|-> y₂)
        (w₂ : y₂ -|-> z₂)
        (τ : h₂ ==> h₂')
        (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
        (s₂ : square_double_bicat h₂' h₃ v₂ w₂),
      s₁ ⋆v (τ ▵s s₂) = (τ ▿s s₁) ⋆v s₂)
     ×
     (∏ (x₁ x₂ x₃ y₁ y₂ y₃ : B)
        (h₁ : x₁ --> x₂)
        (h₂ : x₂ --> x₃)
        (k₁ : y₁ --> y₂)
        (k₂ : y₂ --> y₃)
        (v₁ v₁' : x₁ -|-> y₁)
        (v₂ : x₂ -|-> y₂)
        (v₃ : x₃ -|-> y₃)
        (τ : v₁ =|=> v₁')
        (s₁ : square_double_bicat h₁ k₁ v₁' v₂)
        (s₂ : square_double_bicat h₂ k₂ v₂ v₃),
      τ ◃s (s₁ ⋆h s₂) = (τ ◃s s₁) ⋆h s₂)
     ×
     (∏ (x₁ x₂ x₃ y₁ y₂ y₃ : B)
        (h₁ : x₁ --> x₂)
        (h₂ : x₂ --> x₃)
        (k₁ : y₁ --> y₂)
        (k₂ : y₂ --> y₃)
        (v₁ : x₁ -|-> y₁)
        (v₂ : x₂ -|-> y₂)
        (v₃ v₃' : x₃ -|-> y₃)
        (τ : v₃ =|=> v₃')
        (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
        (s₂ : square_double_bicat h₂ k₂ v₂ v₃),
      τ ▹s (s₁ ⋆h s₂) = s₁ ⋆h (τ ▹s s₂))
     ×
     (∏ (x₁ x₂ x₃ y₁ y₂ y₃ : B)
        (h₁ : x₁ --> x₂)
        (h₂ : x₂ --> x₃)
        (k₁ : y₁ --> y₂)
        (k₂ : y₂ --> y₃)
        (v₁ : x₁ -|-> y₁)
        (v₂ v₂' : x₂ -|-> y₂)
        (v₃ : x₃ -|-> y₃)
        (τ : v₂ =|=> v₂')
        (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
        (s₂ : square_double_bicat h₂ k₂ v₂' v₃),
      s₁ ⋆h (τ ◃s s₂) = (τ ▹s s₁) ⋆h s₂).

Definition whisker_square_bicat_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := lwhisker_square_id_comp_law B
     ×
     rwhisker_square_id_comp_law B
     ×
     uwhisker_square_id_comp_law B
     ×
     dwhisker_square_id_comp_law B
     ×
     whisker_square_compatible B
     ×
     whisker_square_id_square B
     ×
     whisker_square_comp_square B.

(** * 6. Laws relating composition and identity squares (items (ix) and (x) in Verity) *)
Definition double_bicat_interchange_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := ∏ (x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : B)
       (v₁ : x₁ -|-> x₂) (v₁' : x₂ -|-> x₃)
       (v₂ : y₁ -|-> y₂) (v₂' : y₂ -|-> y₃)
       (v₃ : z₁ -|-> z₂) (v₃' : z₂ -|-> z₃)
       (h₁ : x₁ --> y₁)
       (h₂ : y₁ --> z₁)
       (k₁ : x₂ --> y₂)
       (k₂ : y₂ --> z₂)
       (l₁ : x₃ --> y₃)
       (l₂ : y₃ --> z₃)
       (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
       (s₁' : square_double_bicat k₁ l₁ v₁' v₂')
       (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
       (s₂' : square_double_bicat k₂ l₂ v₂' v₃'),
     (s₁ ⋆v s₁') ⋆h (s₂ ⋆v s₂') = (s₁ ⋆h s₂) ⋆v (s₁' ⋆h s₂').

Arguments double_bicat_interchange_law B /.

Definition double_bicat_id_square_laws
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (x : B), id_h_square_bicat (id_v x) = id_v_square_bicat (id_h x))
     ×
     (∏ (x y z : B)
        (h : x -|-> y)
        (k : y -|-> z),
      id_h_square_bicat h ⋆v id_h_square_bicat k = id_h_square_bicat (h · k))
     ×
     (∏ (x y z : B)
        (v : x --> y)
        (w : y --> z),
      id_v_square_bicat v ⋆h id_v_square_bicat w = id_v_square_bicat (v · w)).

Definition double_bicat_id_comp_square_laws
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := double_bicat_interchange_law B × double_bicat_id_square_laws B.

(** * 7. Laws about cylinders (items (vi)-(vii) in Verity) *)
Definition is_hor_cylinder
           {B : ver_bicat_sq_id_comp_whisker}
           {w x y z : B}
           {v₁ : w -|-> y}
           {v₂ : x -|-> z}
           {h₁ h₁' : w --> x}
           {h₂ h₂' : y --> z}
           (s : square_double_bicat h₁ h₂ v₁ v₂)
           (s' : square_double_bicat h₁' h₂' v₁ v₂)
           (τ₁ : h₁ ==> h₁')
           (τ₂ : h₂ ==> h₂')
  : UU
  := τ₂ ▿s s = τ₁ ▵s s'.

Arguments is_hor_cylinder {B w x y z v₁ v₂ h₁ h₁' h₂ h₂'} s s' τ₁ τ₂ /.

Definition is_ver_cylinder
           {B : ver_bicat_sq_id_comp_whisker}
           {w x y z : B}
           {v₁ v₁' : w -|-> y}
           {v₂ v₂' : x -|-> z}
           {h₁ : w --> x}
           {h₂ : y --> z}
           (s : square_double_bicat h₁ h₂ v₁ v₂)
           (s' : square_double_bicat h₁ h₂ v₁' v₂')
           (τ₁ : v₁ =|=> v₁')
           (τ₂ : v₂ =|=> v₂')
  : UU
  := τ₁ ◃s s' = τ₂ ▹s s.

Arguments is_ver_cylinder {B w x y z v₁ v₁' v₂ v₂' h₁ h₂} s s' τ₁ τ₂ /.

Definition associator_cylinder_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : B)
        (h₁ : x₁ --> x₂) (h₂ : x₂ --> x₃) (h₃ : x₃ --> x₄)
        (k₁ : y₁ --> y₂) (k₂ : y₂ --> y₃) (k₃ : y₃ --> y₄)
        (v₁ : x₁ -|-> y₁) (v₂ : x₂ -|-> y₂)
        (v₃ : x₃ -|-> y₃) (v₄ : x₄ -|-> y₄)
        (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
        (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
        (s₃ : square_double_bicat h₃ k₃ v₃ v₄),
      is_hor_cylinder
        (s₁ ⋆h (s₂ ⋆h s₃))
        ((s₁ ⋆h s₂) ⋆h s₃)
        (lassociator _ _ _)
        (lassociator _ _ _))
     ×
     (∏ (w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : B)
        (hw : w₁ --> w₂) (hx : x₁ --> x₂)
        (hy : y₁ --> y₂) (hz : z₁ --> z₂)
        (u₁ : w₁ -|-> x₁) (u₂ : x₁ -|-> y₁) (u₃ : y₁ -|-> z₁)
        (v₁ : w₂ -|-> x₂) (v₂ : x₂ -|-> y₂) (v₃ : y₂ -|-> z₂)
        (s₁ : square_double_bicat hw hx u₁ v₁)
        (s₂ : square_double_bicat hx hy u₂ v₂)
        (s₃ : square_double_bicat hy hz u₃ v₃),
      is_ver_cylinder
        (s₁ ⋆v (s₂ ⋆v s₃))
        ((s₁ ⋆v s₂) ⋆v s₃)
        (lassociator _ _ _)
        (lassociator _ _ _)).

Definition lunitor_cylinder_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      is_hor_cylinder
        (id_h_square_bicat _ ⋆h s)
        s
        (lunitor _)
        (lunitor _))
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      is_ver_cylinder
        (id_v_square_bicat _ ⋆v s)
        s
        (lunitor _)
        (lunitor _)).

Definition runitor_cylinder_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      is_hor_cylinder
        (s ⋆h id_h_square_bicat _)
        s
        (runitor _)
        (runitor _))
     ×
     (∏ (w x y z : B)
        (h₁ : w --> x)
        (h₂ : y --> z)
        (v₁ : w -|-> y)
        (v₂ : x -|-> z)
        (s : square_double_bicat h₁ h₂ v₁ v₂),
      is_ver_cylinder
        (s ⋆v id_v_square_bicat _)
        s
        (runitor _)
        (runitor _)).

Definition comp_cylinder_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := (∏ (x₁ x₂ y₁ y₂ z₁ z₂ : B)
        (h₁ : x₁ --> x₂)
        (h₂ : y₁ --> y₂)
        (h₃ : z₁ --> z₂)
        (v₁ v₁' : x₁ -|-> y₁)
        (v₂ v₂' : y₁ -|-> z₁)
        (w₁ w₁' : x₂ -|-> y₂)
        (w₂ w₂' : y₂ -|-> z₂)
        (τ₁ : v₁ =|=> v₁')
        (τ₂ : v₂ =|=> v₂')
        (θ₁ : w₁ =|=> w₁')
        (θ₂ : w₂ =|=> w₂')
        (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
        (s₁' : square_double_bicat h₁ h₂ v₁' w₁')
        (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
        (s₂' : square_double_bicat h₂ h₃ v₂' w₂')
        (p : is_ver_cylinder s₁ s₁' τ₁ θ₁)
        (q : is_ver_cylinder s₂ s₂' τ₂ θ₂),
      is_ver_cylinder
        (s₁ ⋆v s₂)
        (s₁' ⋆v s₂')
        (τ₁ ⋆ τ₂)
        (θ₁ ⋆ θ₂))
     ×
     (∏ (x₁ x₂ x₃ y₁ y₂ y₃ : B)
        (h₁ h₁' : x₁ --> x₂)
        (h₂ h₂' : x₂ --> x₃)
        (k₁ k₁' : y₁ --> y₂)
        (k₂ k₂' : y₂ --> y₃)
        (v₁ : x₁ -|-> y₁)
        (v₂ : x₂ -|-> y₂)
        (v₃ : x₃ -|-> y₃)
        (τ₁ : h₁ ==> h₁')
        (τ₂ : h₂ ==> h₂')
        (θ₁ : k₁ ==> k₁')
        (θ₂ : k₂ ==> k₂')
        (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
        (s₁' : square_double_bicat h₁' k₁' v₁ v₂)
        (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
        (s₂' : square_double_bicat h₂' k₂' v₂ v₃)
        (p : is_hor_cylinder s₁ s₁' τ₁ θ₁)
        (q : is_hor_cylinder s₂ s₂' τ₂ θ₂),
      is_hor_cylinder
        (s₁ ⋆h s₂)
        (s₁' ⋆h s₂')
        (τ₁ ⋆ τ₂)
        (θ₁ ⋆ θ₂)).

Definition double_bicat_cylinder_laws
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := associator_cylinder_law B
     ×
     lunitor_cylinder_law B
     ×
     runitor_cylinder_law B
     ×
     comp_cylinder_law B.

(** * 8. Verity double bicategories *)
Definition isaset_square_double_bicat_law
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := ∏ (w x y z : B)
       (h₁ : w --> x)
       (h₂ : y --> z)
       (v₁ : w -|-> y)
       (v₂ : x -|-> z),
     isaset (square_double_bicat h₁ h₂ v₁ v₂).

Definition double_bicat_laws
           (B : ver_bicat_sq_id_comp_whisker)
  : UU
  := whisker_square_bicat_law B
     ×
     double_bicat_id_comp_square_laws B
     ×
     double_bicat_cylinder_laws B
     ×
     isaset_square_double_bicat_law B.

Proposition make_double_bicat_laws
            (B : ver_bicat_sq_id_comp_whisker)
            (H₁ : whisker_square_bicat_law B)
            (H₂ : double_bicat_id_comp_square_laws B)
            (H₃ : double_bicat_cylinder_laws B)
            (H₄ : isaset_square_double_bicat_law B)
  : double_bicat_laws B.
Proof.
  exact (H₁ ,, H₂ ,, H₃ ,, H₄).
Defined.

Definition verity_double_bicat
  : UU
  := ∑ (B : ver_bicat_sq_id_comp_whisker),
     double_bicat_laws B.

Definition make_verity_double_bicat
           (B : ver_bicat_sq_id_comp_whisker)
           (H : double_bicat_laws B)
  : verity_double_bicat
  := B ,, H.

Coercion verity_double_bicat_to_ver_bicat_sq_id_comp_whisker
         (B : verity_double_bicat)
  : ver_bicat_sq_id_comp_whisker
  := pr1 B.

(** * 9. Unfolded versions of the laws for Verity double bicategories *)
Section VerityBicatLawsAccessors.
  Context (B : verity_double_bicat).

  Proposition lwhisker_square_id
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : id2 v₁ ◃s s = s.
  Proof.
    exact (pr1 (pr1 (pr12 B)) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition lwhisker_square_comp
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ v₁' v₁'' : w -|-> y}
              {v₂ : x -|-> z}
              (τ₁ : v₁ =|=> v₁')
              (τ₂ : v₁' =|=> v₁'')
              (s : square_double_bicat h₁ h₂ v₁'' v₂)
    : (τ₁ • τ₂) ◃s s = τ₁ ◃s (τ₂ ◃s s).
  Proof.
    exact (pr2 (pr1 (pr12 B)) _ _ _ _ _ _ _ _ _ _ τ₁ τ₂ s).
  Defined.

  Proposition rwhisker_square_id
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : id2 v₂ ▹s s = s.
  Proof.
    exact (pr1 (pr12 (pr12 B)) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition rwhisker_square_comp
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ v₂' v₂'' : x -|-> z}
              (τ₁ : v₂ =|=> v₂')
              (τ₂ : v₂' =|=> v₂'')
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : (τ₁ • τ₂) ▹s s = τ₂ ▹s (τ₁ ▹s s).
  Proof.
    exact (pr2 (pr12 (pr12 B)) _ _ _ _ _ _ _ _ _ _ τ₁ τ₂ s).
  Defined.

  Proposition uwhisker_square_id
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : id2 h₁ ▵s s = s.
  Proof.
    exact (pr1 (pr122 (pr12 B)) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition uwhisker_square_comp
              {w x y z : B}
              {h₁ h₁' h₁'' : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (τ₁ : h₁ ==> h₁')
              (τ₂ : h₁' ==> h₁'')
              (s : square_double_bicat h₁'' h₂ v₁ v₂)
    : (τ₁ • τ₂) ▵s s = τ₁ ▵s (τ₂ ▵s s).
  Proof.
    exact (pr2 (pr122 (pr12 B)) _ _ _ _ _ _ _ _ _ _ τ₁ τ₂ s).
  Defined.

  Proposition dwhisker_square_id
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : id2 h₂ ▿s s = s.
  Proof.
    exact (pr1 (pr1 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition dwhisker_square_comp
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ h₂' h₂'' : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (τ₁ : h₂ ==> h₂')
              (τ₂ : h₂' ==> h₂'')
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : (τ₁ • τ₂) ▿s s = τ₂ ▿s (τ₁ ▿s s).
  Proof.
    exact (pr2 (pr1 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ _ _ τ₁ τ₂ s).
  Defined.

  Proposition dwhisker_uwhisker_square
              {w x y z : B}
              {h₁ h₁' : w --> x}
              {h₂ h₂' : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (τ : h₁ ==> h₁')
              (θ : h₂ ==> h₂')
              (s : square_double_bicat h₁' h₂ v₁ v₂)
    : θ ▿s (τ ▵s s) = τ ▵s (θ ▿s s).
  Proof.
    exact (pr1 (pr12 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ _ _ τ θ s).
  Defined.

  Proposition lwhisker_uwhisker_square
              {w x y z : B}
              {h₁ h₁' : w --> x}
              {h₂ : y --> z}
              {v₁ v₁' : w -|-> y}
              {v₂ : x -|-> z}
              (τ : h₁ ==> h₁')
              (θ : v₁ ==> v₁')
              (s : square_double_bicat h₁' h₂ v₁' v₂)
    : θ ◃s (τ ▵s s) = τ ▵s (θ ◃s s).
  Proof.
    exact (pr12 (pr12 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ _ _ τ θ s).
  Defined.

  Proposition rwhisker_uwhisker_square
              {w x y z : B}
              {h₁ h₁' : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ v₂' : x -|-> z}
              (τ : h₁ ==> h₁')
              (θ : v₂ ==> v₂')
              (s : square_double_bicat h₁' h₂ v₁ v₂)
    : θ ▹s (τ ▵s s) = τ ▵s (θ ▹s s).
  Proof.
    exact (pr122 (pr12 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ _ _ τ θ s).
  Defined.

  Proposition lwhisker_dwhisker_square
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ h₂' : y --> z}
              {v₁ v₁' : w -|-> y}
              {v₂ : x -|-> z}
              (τ : h₂ ==> h₂')
              (θ : v₁ =|=> v₁')
              (s : square_double_bicat h₁ h₂ v₁' v₂)
    : θ ◃s (τ ▿s s) = τ ▿s (θ ◃s s).
  Proof.
    exact (pr1 (pr222 (pr12 (pr222 (pr12 B)))) _ _ _ _ _ _ _ _ _ _ τ θ s).
  Defined.

  Definition rwhisker_dwhisker_square
             {w x y z : B}
             {h₁ : w --> x}
             {h₂ h₂' : y --> z}
             {v₁ : w -|-> y}
             {v₂ v₂' : x -|-> z}
             (τ : h₂ ==> h₂')
             (θ : v₂ =|=> v₂')
             (s : square_double_bicat h₁ h₂ v₁ v₂)
    : θ ▹s (τ ▿s s) = τ ▿s (θ ▹s s).
  Proof.
    exact (pr12 (pr222 (pr12 (pr222 (pr12 B)))) _ _ _ _ _ _ _ _ _ _ τ θ s).
  Defined.

  Proposition rwhisker_lwhisker_square
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ v₁' : w -|-> y}
              {v₂ v₂' : x -|-> z}
              (τ : v₁ =|=> v₁')
              (θ : v₂ =|=> v₂')
              (s : square_double_bicat h₁ h₂ v₁' v₂)
    : θ ▹s (τ ◃s s) = τ ◃s (θ ▹s s).
  Proof.
    exact (pr22 (pr222 (pr12 (pr222 (pr12 B)))) _ _ _ _ _ _ _ _ _ _ τ θ s).
  Defined.

  Proposition lwhisker_id_h_square
              {x y : B}
              {v w : x -|-> y}
              (τ : v =|=> w)
    : τ ◃s id_h_square_bicat w = τ ▹s id_h_square_bicat v.
  Proof.
    exact (pr1 (pr122 (pr222 (pr12 B))) _ _ _ _ τ).
  Defined.

  Proposition uwhisker_id_v_square
              {x y : B}
              {h k : x --> y}
              (τ : h ==> k)
    : τ ▵s id_v_square_bicat k = τ ▿s id_v_square_bicat h.
  Proof.
    exact (pr2 (pr122 (pr222 (pr12 B))) _ _ _ _ τ).
  Defined.

  Proposition uwhisker_vcomp_square
              {x₁ x₂ y₁ y₂ z₁ z₂ : B}
              {h₁ h₁' : x₁ --> x₂}
              {h₂ : y₁ --> y₂}
              {h₃ : z₁ --> z₂}
              {v₁ : x₁ -|-> y₁}
              {v₂ : y₁ -|-> z₁}
              {w₁ : x₂ -|-> y₂}
              {w₂ : y₂ -|-> z₂}
              (τ : h₁ ==> h₁')
              (s₁ : square_double_bicat h₁' h₂ v₁ w₁)
              (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
    : τ ▵s (s₁ ⋆v s₂) = (τ ▵s s₁) ⋆v s₂.
  Proof.
    exact (pr1 (pr222 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ s₁ s₂).
  Defined.

  Proposition dwhisker_vcomp_square
              {x₁ x₂ y₁ y₂ z₁ z₂ : B}
              {h₁ : x₁ --> x₂}
              {h₂ : y₁ --> y₂}
              {h₃ h₃' : z₁ --> z₂}
              {v₁ : x₁ -|-> y₁}
              {v₂ : y₁ -|-> z₁}
              {w₁ : x₂ -|-> y₂}
              {w₂ : y₂ -|-> z₂}
              (τ : h₃ ==> h₃')
              (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
              (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
    : τ ▿s (s₁ ⋆v s₂) = s₁ ⋆v (τ ▿s s₂).
  Proof.
    exact (pr12 (pr222 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ s₁ s₂).
  Defined.

  Proposition ud_whisker_vcomp_square
              {x₁ x₂ y₁ y₂ z₁ z₂ : B}
              {h₁ : x₁ --> x₂}
              {h₂ h₂' : y₁ --> y₂}
              {h₃ : z₁ --> z₂}
              {v₁ : x₁ -|-> y₁}
              {v₂ : y₁ -|-> z₁}
              {w₁ : x₂ -|-> y₂}
              {w₂ : y₂ -|-> z₂}
              (τ : h₂ ==> h₂')
              (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
              (s₂ : square_double_bicat h₂' h₃ v₂ w₂)
    : s₁ ⋆v (τ ▵s s₂) = (τ ▿s s₁) ⋆v s₂.
  Proof.
    exact (pr122 (pr222 (pr222 (pr12 B))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ s₁ s₂).
  Defined.

  Proposition lwhisker_hcomp_square
              {x₁ x₂ x₃ y₁ y₂ y₃ : B}
              {h₁ : x₁ --> x₂}
              {h₂ : x₂ --> x₃}
              {k₁ : y₁ --> y₂}
              {k₂ : y₂ --> y₃}
              {v₁ v₁' : x₁ -|-> y₁}
              {v₂ : x₂ -|-> y₂}
              {v₃ : x₃ -|-> y₃}
              (τ : v₁ =|=> v₁')
              (s₁ : square_double_bicat h₁ k₁ v₁' v₂)
              (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
    : τ ◃s (s₁ ⋆h s₂) = (τ ◃s s₁) ⋆h s₂.
  Proof.
    exact (pr1 (pr222 (pr222 (pr222 (pr12 B)))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ s₁ s₂).
  Defined.

  Proposition rwhisker_hcomp_square
              {x₁ x₂ x₃ y₁ y₂ y₃ : B}
              {h₁ : x₁ --> x₂}
              {h₂ : x₂ --> x₃}
              {k₁ : y₁ --> y₂}
              {k₂ : y₂ --> y₃}
              {v₁ : x₁ -|-> y₁}
              {v₂ : x₂ -|-> y₂}
              {v₃ v₃' : x₃ -|-> y₃}
              (τ : v₃ =|=> v₃')
              (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
              (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
    : τ ▹s (s₁ ⋆h s₂) = s₁ ⋆h (τ ▹s s₂).
  Proof.
    exact (pr12 (pr222 (pr222 (pr222 (pr12 B)))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ s₁ s₂).
  Defined.

  Proposition lrwhisker_hcomp_square
              {x₁ x₂ x₃ y₁ y₂ y₃ : B}
              {h₁ : x₁ --> x₂}
              {h₂ : x₂ --> x₃}
              {k₁ : y₁ --> y₂}
              {k₂ : y₂ --> y₃}
              {v₁ : x₁ -|-> y₁}
              {v₂ v₂' : x₂ -|-> y₂}
              {v₃ : x₃ -|-> y₃}
              (τ : v₂ =|=> v₂')
              (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
              (s₂ : square_double_bicat h₂ k₂ v₂' v₃)
    : s₁ ⋆h (τ ◃s s₂) = (τ ▹s s₁) ⋆h s₂.
  Proof.
    exact (pr22 (pr222 (pr222 (pr222 (pr12 B)))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ s₁ s₂).
  Defined.

  Proposition double_bicat_interchange
              {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : B}
              {v₁ : x₁ -|-> x₂} {v₁' : x₂ -|-> x₃}
              {v₂ : y₁ -|-> y₂} {v₂' : y₂ -|-> y₃}
              {v₃ : z₁ -|-> z₂} {v₃' : z₂ -|-> z₃}
              {h₁ : x₁ --> y₁}
              {h₂ : y₁ --> z₁}
              {k₁ : x₂ --> y₂}
              {k₂ : y₂ --> z₂}
              {l₁ : x₃ --> y₃}
              {l₂ : y₃ --> z₃}
              (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
              (s₁' : square_double_bicat k₁ l₁ v₁' v₂')
              (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
              (s₂' : square_double_bicat k₂ l₂ v₂' v₃')
    : (s₁ ⋆v s₁') ⋆h (s₂ ⋆v s₂') = (s₁ ⋆h s₂) ⋆v (s₁' ⋆h s₂').
  Proof.
    exact (pr1 (pr122 B) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₁' s₂ s₂').
  Defined.

  Proposition id_h_square_bicat_id
              (x : B)
    : id_h_square_bicat (id_v x) = id_v_square_bicat (id_h x).
  Proof.
    exact (pr1 (pr2 (pr122 B)) x).
  Defined.

  Proposition id_h_square_bicat_comp
              {x y z : B}
              (h : x -|-> y)
              (k : y -|-> z)
    : id_h_square_bicat h ⋆v id_h_square_bicat k = id_h_square_bicat (h · k).
  Proof.
    exact (pr12 (pr2 (pr122 B)) _ _ _ h k).
  Defined.

  Proposition id_v_square_bicat_comp
              {x y z : B}
              (v : x --> y)
              (w : y --> z)
    : id_v_square_bicat v ⋆h id_v_square_bicat w = id_v_square_bicat (v · w).
  Proof.
    exact (pr22 (pr2 (pr122 B)) _ _ _ v w).
  Defined.

  Proposition lassociator_h_comp_square
              {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : B}
              {h₁ : x₁ --> x₂} {h₂ : x₂ --> x₃} {h₃ : x₃ --> x₄}
              {k₁ : y₁ --> y₂} {k₂ : y₂ --> y₃} {k₃ : y₃ --> y₄}
              {v₁ : x₁ -|-> y₁} {v₂ : x₂ -|-> y₂}
              {v₃ : x₃ -|-> y₃} {v₄ : x₄ -|-> y₄}
              (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
              (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
              (s₃ : square_double_bicat h₃ k₃ v₃ v₄)
    : lassociator k₁ k₂ k₃ ▿s s₁ ⋆h (s₂ ⋆h s₃)
      =
      lassociator h₁ h₂ h₃ ▵s s₁ ⋆h s₂ ⋆h s₃.
  Proof.
    exact (pr11 (pr1 (pr222 B)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂ s₃).
  Defined.

  Proposition lassociator_v_comp_square
              {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : B}
              {hw : w₁ --> w₂} {hx : x₁ --> x₂}
              {hy : y₁ --> y₂} {hz : z₁ --> z₂}
              {u₁ : w₁ -|-> x₁} {u₂ : x₁ -|-> y₁} {u₃ : y₁ -|-> z₁}
              {v₁ : w₂ -|-> x₂} {v₂ : x₂ -|-> y₂} {v₃ : y₂ -|-> z₂}
              (s₁ : square_double_bicat hw hx u₁ v₁)
              (s₂ : square_double_bicat hx hy u₂ v₂)
              (s₃ : square_double_bicat hy hz u₃ v₃)
    : lassociator u₁ u₂ u₃ ◃s s₁ ⋆v s₂ ⋆v s₃
      =
      lassociator v₁ v₂ v₃ ▹s s₁ ⋆v (s₂ ⋆v s₃).
  Proof.
    exact (pr21 (pr1 (pr222 B)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂ s₃).
  Defined.

  Proposition lunitor_h_comp_square
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : lunitor h₂ ▿s id_h_square_bicat v₁ ⋆h s
      =
      lunitor h₁ ▵s s.
  Proof.
    exact (pr1 (pr12 (pr1 (pr222 B))) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition lunitor_v_comp_square
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : lunitor v₁ ◃s s
      =
      lunitor v₂ ▹s id_v_square_bicat h₁ ⋆v s.
  Proof.
    exact (pr2 (pr12 (pr1 (pr222 B))) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition runitor_h_comp_square
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : runitor h₂ ▿s s ⋆h id_h_square_bicat v₂
      =
      runitor h₁ ▵s s.
  Proof.
    exact (pr1 (pr122 (pr1 (pr222 B))) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition runitor_v_comp_square
              {w x y z : B}
              {h₁ : w --> x}
              {h₂ : y --> z}
              {v₁ : w -|-> y}
              {v₂ : x -|-> z}
              (s : square_double_bicat h₁ h₂ v₁ v₂)
    : runitor v₁ ◃s s
      =
      runitor v₂ ▹s s ⋆v id_v_square_bicat h₂.
  Proof.
    exact (pr2 (pr122 (pr1 (pr222 B))) _ _ _ _ _ _ _ _ s).
  Defined.

  Proposition ver_bicat_hcomp_v_comp_square
              {x₁ x₂ y₁ y₂ z₁ z₂ : B}
              {h₁ : x₁ --> x₂}
              {h₂ : y₁ --> y₂}
              {h₃ : z₁ --> z₂}
              {v₁ v₁' : x₁ -|-> y₁}
              {v₂ v₂' : y₁ -|-> z₁}
              {w₁ w₁' : x₂ -|-> y₂}
              {w₂ w₂' : y₂ -|-> z₂}
              (τ₁ : v₁ =|=> v₁')
              (τ₂ : v₂ =|=> v₂')
              (θ₁ : w₁ =|=> w₁')
              (θ₂ : w₂ =|=> w₂')
              (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
              (s₁' : square_double_bicat h₁ h₂ v₁' w₁')
              (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
              (s₂' : square_double_bicat h₂ h₃ v₂' w₂')
              (p : τ₁ ◃s s₁' = θ₁ ▹s s₁)
              (q : τ₂ ◃s s₂' = θ₂ ▹s s₂)
    : (τ₂ ⋆⋆ τ₁) ◃s s₁' ⋆v s₂'
      =
      (θ₂ ⋆⋆ θ₁) ▹s s₁ ⋆v s₂.
  Proof.
    exact (pr1 (pr222 (pr1 (pr222 B))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p q).
  Defined.

  Proposition hor_bicat_hcomp_h_comp_square
              {x₁ x₂ x₃ y₁ y₂ y₃ : B}
              {h₁ h₁' : x₁ --> x₂}
              {h₂ h₂' : x₂ --> x₃}
              {k₁ k₁' : y₁ --> y₂}
              {k₂ k₂' : y₂ --> y₃}
              {v₁ : x₁ -|-> y₁}
              {v₂ : x₂ -|-> y₂}
              {v₃ : x₃ -|-> y₃}
              (τ₁ : h₁ ==> h₁')
              (τ₂ : h₂ ==> h₂')
              (θ₁ : k₁ ==> k₁')
              (θ₂ : k₂ ==> k₂')
              (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
              (s₁' : square_double_bicat h₁' k₁' v₁ v₂)
              (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
              (s₂' : square_double_bicat h₂' k₂' v₂ v₃)
              (p : θ₁ ▿s s₁ = τ₁ ▵s s₁')
              (q : θ₂ ▿s s₂ = τ₂ ▵s s₂')
    : (θ₂ ⋆⋆ θ₁) ▿s s₁ ⋆h s₂
      =
      (τ₂ ⋆⋆ τ₁) ▵s s₁' ⋆h s₂'.
  Proof.
    exact (pr2 (pr222 (pr1 (pr222 B))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p q).
  Defined.

  Proposition isaset_square_double_bicat
              {w x y z : B}
              (h₁ : w --> x)
              (h₂ : y --> z)
              (v₁ : w -|-> y)
              (v₂ : x -|-> z)
    : isaset (square_double_bicat h₁ h₂ v₁ v₂).
  Proof.
    exact (pr2 (pr222 B) _ _ _ _ h₁ h₂ v₁ v₂).
  Defined.
End VerityBicatLawsAccessors.
