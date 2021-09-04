Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Topology.Topology.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.preorder_categories.
Require Import UniMath.CategoryTheory.categories.commrings.
Require Import UniMath.AlgebraicGeometry.Topology.

Local Open Scope cat.
Local Open Scope logic.
Local Open Scope subtype.
Local Open Scope open.


(* The category of open subsets of a topological space. *)

Section open_category.
  Context (X : TopologicalSet).

  Definition open_po : po (@Open X) :=
    make_po _ (isporesrel _ _ (subtype_containment_ispreorder X)).

  Definition open_category : category := po_category open_po.
End open_category.


Section sheaf_commring_prop.
  Context {X : TopologicalSet}
          (F' : functor_data (open_category X)^op commring_precategory).

  Definition F (U : Open) : commring := F' U.

  Definition restriction {U V : Open} (H : U ⊆ V) : ringfun (F V) (F U) := #F' H.

  Definition restrict {A : hsubtype Open} (f : F (⋃ A)) (U : A) : F (pr1 U) :=
    restriction (contained_in_union_open U) f.

  Definition agree_on_intersections {A : hsubtype Open}
                                    (g : ∏ U : A, F (pr1 U)) : UU :=
    ∏ U V : A, restriction (intersection_contained1 _ _) (g U) =
               restriction (intersection_contained2 _ _) (g V).

  Definition locality : hProp := ∀ (A : hsubtype Open) (f g : F (⋃ A)),
      restrict f ~ restrict g ⇒ f = g.

  Definition gluing : hProp := ∀ (A : hsubtype Open) (g : ∏ U : A, F (pr1 U)),
      agree_on_intersections g ⇒ ∃ f, restrict f ~ g.
End sheaf_commring_prop.


Section sheaf_commring.
  Context {X : TopologicalSet}.

  Definition sheaf_commring : UU :=
    ∑ F : (open_category X)^op ⟶ commring_precategory, locality F ∧ gluing F.

  Definition make_sheaf_commring F l g : sheaf_commring := F ,, l ,, g.

  Definition sheaf_commring_functor (F : sheaf_commring) :
    (open_category X)^op ⟶ commring_precategory := pr1 F.
  Coercion sheaf_commring_functor : sheaf_commring >-> functor.

  Definition sheaf_commring_locality (F : sheaf_commring) : locality F := pr12 F.

  Definition sheaf_commring_gluing (F : sheaf_commring) : gluing F := pr22 F.
End sheaf_commring.

Arguments sheaf_commring _ : clear implicits.
