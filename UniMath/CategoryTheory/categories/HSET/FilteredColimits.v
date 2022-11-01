Require Import UniMath.Foundations.All.

Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.QuotientSet.
Require Import UniMath.MoreFoundations.Subtypes.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.Filtered.
Require Import UniMath.CategoryTheory.limits.StandardDiagrams.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.KFiniteTypes.
Require Import UniMath.Combinatorics.KFiniteSubtypes.

(** * Filtered Colimits of Sets.

  1. Filtered colimits as set quotients.
  2. The category of K-finite subsets of a set is filtered. [is_filtered_kfinite_subsets].
  3. Every set is the filtered colimit of its K-finite subsets. [is_colimit_kfinite_subsets]
  4. Compact sets are K-finite. [iskfinite_compact_SET]

*)

Local Open Scope cat.
Local Open Scope subtype.

(** Given a filtered category J and a diagram F : J -> SET the colimit of F can be
    constructed as a quotient of the disjoint union, ∐ⱼF(j)/~, where (j₁, x) ~ (j₂, y)
    if there is some i ∈ J and edges u : j₁ -> i, v : j₂ -> i (in J) such that
               F(u) x = F(v) y.

    See [filtered_cobase_rel].
 *)
Section filtered_colimits_in_SET.
  (**
   1. Filtered colimits as set quotients.
   *)
  Variable J : category.
  Variable Jfiltered : is_filtered J.
  Variable F : functor J SET.

  Let d := (pr1 F) : diagram J SET.

  (* This follows the same basic structure used in HSET.Colimits *)
  Definition cobase : UU
    := ∑ (j : vertex J), (dob d j : hSet).

  Local Definition cobasepr1 : cobase -> vertex J := pr1.
  Local Coercion cobasepr1 : cobase >-> vertex.

  Local Definition cobasept : ∏ (a : cobase), (dob d a) : hSet := pr2.
  Local Coercion cobasept : cobase >-> pr1hSet.

  Definition filtered_cobase_rel : hrel cobase
    := λ (a b : cobase),
      ∥ ∑ (c : J) (fia : edge a c) (fib : edge b c),
      (dmor d fia) a = (dmor d fib) b ∥.

  Definition filtered_rel : hrel cobase
    := eqrel_from_hrel filtered_cobase_rel.

  Definition filtered_eqrel : eqrel cobase.
  Proof.
    use make_eqrel.
    - exact(eqrel_from_hrel filtered_cobase_rel).
    - apply iseqrel_eqrel_from_hrel.
  Defined.

  (* TODO: Redo this but using setquot2 instead. *)
  Definition FilteredColimitSET : SET
    := make_hSet
         (setquot filtered_eqrel)
         (isasetsetquot filtered_eqrel).

  (* Define the injections from the diagram into the colimit. *)
  Definition inject (j : vertex J) : SET⟦dob d j, FilteredColimitSET⟧
    := λ (dj : dob d j : hSet),
      setquotpr filtered_eqrel (j ,, dj).

  (* They satisfy the cocone property. This is where we use the assumption
     that J is filtered. *)
  Lemma filtered_forms_cocone : forms_cocone d inject.
  Proof.
    intros u v e.
    apply funextfun; intros x.

    apply(weqpathsinsetquot filtered_eqrel).
    apply eqrel_impl.

    (* Here ↓ is Jfiltered used. *)
    use(hinhfun _ (Jfiltered _ (make_interval_diagram u v e) (is_finite_graph_interval))).

    intros P; destruct P as [apex cc]; cbn.

    exists apex.
    exists (coconeIn cc false).
    exists (coconeIn cc true).

    (* This is to convince Coq that we can use eqtohomot. *)
    change (dmor d (coconeIn cc false) (dmor d e x))
      with ((dmor d e · (dmor d (coconeIn cc false))) x).
    use(eqtohomot _ x).
    etrans; [apply(!functor_comp F e (coconeIn cc false)) |]; apply maponpaths.
    exact(coconeInCommutes cc true false tt).
  Qed.

  Definition filtered_cocone : cocone d FilteredColimitSET.
  Proof.
    use make_cocone.
    - exact inject.
    - exact filtered_forms_cocone.
  Defined.

  Definition from_cobase {Y : SET} (cc : cocone d Y) : cobase -> Y : hSet
    := λ (a : cobase), coconeIn cc a a.

  Definition from_cobase_hrel {Y : SET} (cc : cocone d Y) : hrel cobase.
  Proof.
    intros a b.
    use make_hProp.
    - exact(from_cobase cc a = from_cobase cc b).
    - apply setproperty.
  Defined.

  Definition from_cobase_eqrel {Y : SET} (cc : cocone d Y) : eqrel cobase.
  Proof.
    use make_eqrel.
    - exact(from_cobase_hrel cc).
    - abstract(repeat split; red; intros *; [apply pathscomp0 | apply pathsinv0]).
  Defined.

  Definition filtered_cobase_rel_impl {Y : SET}
    (cc : cocone d Y)
    (a b : cobase)
    (Rab : filtered_cobase_rel a b)
    : from_cobase_eqrel cc a b.
  Proof.
    use Rab; intros h.
    etrans; [refine(!eqtohomot (coconeInCommutes cc _ _ _) a); exact(pr12 h) |].
    etrans; [| refine(eqtohomot (coconeInCommutes cc _ _ _) b); exact(pr122 h)].
    apply(maponpaths _ (pr222 h)).
  Defined.

  Definition filtered_rel_impl {Y : SET}
    (cc : cocone d Y)
    (a b : cobase)
    (Rab : filtered_rel a b)
    : from_cobase_eqrel cc a b.
  Proof.
    now apply(minimal_eqrel_from_hrel filtered_cobase_rel);
      [apply filtered_cobase_rel_impl |].
  Defined.

  Definition iscomprelfun_from_cobase {Y : SET}
    (cc : cocone d Y)
    : iscomprelfun filtered_rel (from_cobase cc).
  Proof.
    red; intros *.
    apply filtered_rel_impl.
  Defined.

  Definition filtered_cocone_morphism {Y : SET}
    (cc : cocone d Y)
    : SET⟦FilteredColimitSET, Y⟧.
  Proof.
    use setquotuniv.
    - exact(from_cobase cc).
    - exact(iscomprelfun_from_cobase cc).
  Defined.

  Lemma is_cocone_mor_filtered_cocone_morphism {Y : SET}
    (cc : cocone d Y)
    : is_cocone_mor (filtered_cocone) cc (filtered_cocone_morphism cc).
  Proof.
    intro; apply idpath.
  Qed.

  Lemma is_unique_filtered_cocone_morphism {Y : SET}
    (cc : cocone d Y)
    (f : SET⟦FilteredColimitSET, Y⟧)
    (fmor : is_cocone_mor filtered_cocone cc f)
    : f = filtered_cocone_morphism cc.
  Proof.
    apply funextfun; intro x.
    apply(surjectionisepitosets (setquotpr filtered_eqrel)).
    - apply issurjsetquotpr.
    - apply setproperty.
    - intro b. exact(eqtohomot (fmor b) b).
  Qed.

  Definition FilteredColimCoconeSET : ColimCocone d.
  Proof.
    use make_ColimCocone.
    - exact FilteredColimitSET.
    - exact filtered_cocone.
    - intros Y cc.
      use unique_exists.
      + exact(filtered_cocone_morphism cc).
      + exact(is_cocone_mor_filtered_cocone_morphism cc).
      + exact(isaprop_is_cocone_mor filtered_cocone cc).
      + exact(is_unique_filtered_cocone_morphism cc).
  Defined.
End filtered_colimits_in_SET.

Section category_of_kfinite_subsets.
  (**
   2. The category of K-finite subsets of a set, with subset inclusions as morphisms.

     - [kfinite_subsets_category]
     - [is_filtered_kfinite_subsets]
   *)

  Definition kfinite_subsets_ob_mor (X : hSet) : precategory_ob_mor.
  Proof.
    (* we are actually taking the K-finite sub/types/ as objects
       and subtype-containment as morphisms between them. But the
       corresponding carriers really are sets, thanks to isaset_carrier_subset.
     *)
    use make_precategory_ob_mor.
    - exact(kfinite_subtype X).
    - exact(subtype_containedIn). (* ⊆ *)
  Defined.

  Definition kfinite_subsets_precategory_data (X : hSet)
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact(kfinite_subsets_ob_mor X).
    - intro; apply subtype_containment_isrefl.
    - intros *; apply subtype_containment_istrans.
  Defined.

  Definition kfinite_subsets_precategory (X : hSet)
    : precategory.
  Proof.
    use make_precategory.
    - exact(kfinite_subsets_precategory_data X).
    - repeat split. (* Solves everything by applying idpath. *)
  Defined.

  Lemma has_homsets_kfinite_subsets (X : hSet)
    : has_homsets (kfinite_subsets_precategory X).
  Proof.
    red; intros.
    apply isasetaprop.
    apply propproperty.
  Qed.

  Definition kfinite_subsets_category (X : hSet) : category.
  Proof.
    use make_category.
    - exact(kfinite_subsets_precategory X).
    - exact(has_homsets_kfinite_subsets X).
  Defined.

  Lemma is_filtered_kfinite_subsets (X : hSet)
    : is_filtered (kfinite_subsets_category X).
  Proof.
    intros g d gfinite.
    apply hinhpr.

    simple refine(_ ,, _).
    - exact(kfinite_subtype_union (dob d) (finite_vertexset gfinite)).
    - use make_cocone.
      + apply subtype_union_containedIn.
      + abstract(red; intros
                 ; apply funextsec; intro
                 ; apply funextsec; intro
                 ; apply squash_path).
  Qed.

  (* Define the functor from kfinite_subsets_category X into SET sending each
     subtype to its carrier set and each ⊆ to the inclusion between carriers.
   *)

  Definition kfinite_subsets_functor_data (X : hSet)
    : functor_data (kfinite_subsets_category X) SET.
  Proof.
    use make_functor_data.
    - exact(λ (A : kfinite_subtype X), carrier_set A).
    - exact(λ _ _ E, subtype_inc E).
  Defined.

  Definition kfinite_subsets_functor (X : hSet)
    : functor (kfinite_subsets_category X) SET.
  Proof.
    use make_functor.
    - exact(kfinite_subsets_functor_data X).
    - abstract(split; (red; intros; apply idpath)).
  Defined.

End category_of_kfinite_subsets.

Section colimit_of_kfinite_subsets.

  (**
   3. Proof that every set is the filtered colimit of its K-finite subsets.
  *)

  Variable X : hSet.
  Let d := kfinite_subsets_functor_data X. (* The diagram of kfinite subsets. *)

  Definition kfinite_subsets_cocone : cocone d X.
  Proof.
    use make_cocone.
    - exact(λ (A : kfinite_subtype X), pr1).
    - abstract(red; intros; apply idpath).
  Defined.

  Definition is_colimit_kfinite_subsets : isColimCocone d X kfinite_subsets_cocone.
  Proof.
    intros Y cc.
    use unique_exists.
    - intro x. exact(coconeIn cc (kfinite_subtype_singleton x) singleton_point).
    - abstract(intro A; apply funextfun; intro x;
               set (commutes := coconeInCommutes cc
                                  (kfinite_subtype_singleton (pr1 x))
                                  A
                                  (singleton_is_in _ x));
               apply(eqtohomot (!commutes))).
    - intro; apply isaprop_is_cocone_mor.
    - abstract(intros f fmor; apply funextfun; intro x;
               exact(eqtohomot (fmor (kfinite_subtype_singleton x))
                       singleton_point)).
  Defined.

End colimit_of_kfinite_subsets.

Section compact_sets_are_kfinite.
  (**
   4. Compact sets are K-finite.
   *)

  Variable X : SET.

  (* We can always map the kfinite_subsets_cocone to a cocone with apex
     Hom(X, X) over Hom(X, -) applied to the kfinite_subsets-diagram.
     In general this will not be a colimit, but if X is compact it
     will be. *)

  Local Definition homD := (mapdiagram (hom X) (kfinite_subsets_functor_data X)).

  Local Definition homcocone : cocone homD (hom X X).
  Proof.
    apply mapcocone.
    exact(kfinite_subsets_cocone X).
  Defined.

  Definition is_colimit_homcocone
    (comp : is_compact X)
    : isColimCocone homD (hom X X) homcocone.
  Proof.
    use comp.
    - exact(is_filtered_kfinite_subsets X).
    - exact(is_colimit_kfinite_subsets X).
  Defined.

  (* If X is compact then Hom(X, X) is a colimit. We call it homXX here. *)
  Local Definition homXX (comp : is_compact X) : ColimCocone homD.
  Proof.
    use make_ColimCocone.
    - exact(hom X X).
    - exact homcocone.
    - exact(is_colimit_homcocone comp).
  Defined.

  (* Define filtCC to be the filtered colimit (defined as a set quotient above) of
     hom(X, -) applied to the diagram of K-finite subsets. The idea is to use that
     the canonical cocone morphism
                           φ : colim filtCC --> (hom X X)
     is an isomorphism when X is compact, together with the explicit construction
     of filtered colimits of sets to conclude that there is some K-finite subset
                          Xᵢ ⊆ X
     where the inclusion Xᵢ --> X is surjective.
   *)

  Local Definition filtCC := FilteredColimCoconeSET
                               (kfinite_subsets_category X)
                               (is_filtered_kfinite_subsets X)
                               ((kfinite_subsets_functor X) ∙ (hom X)).


  Local Definition φ : colim filtCC --> (hom X X).
  Proof.
    use colimArrow.
    exact homcocone.
  Defined.

  Local Definition φiso (comp : is_compact X) : is_z_isomorphism φ.
  Proof.
    use isColim_is_z_iso.
    use comp.
    - exact(is_filtered_kfinite_subsets X).
    - exact(is_colimit_kfinite_subsets X).
  Qed.

  (* Proof idea: take (identity X) ∈ Hom(X, X). The image φinv(identity X) ∈ filtCC
     can be deconstructed as an element in the cobase of the diagram of the hom-mapped
     diagram of K-finite subsets, i.e. it is represented by some function (f : X --> Xᵢ)
     for some K-finite subset of X.

     Then prove that the inclusion Xᵢ ⊆ X is a surjection by applying f to the fibers
     and use commutativity of the cocone morphism φ.
   *)

  Lemma iskfinite_compact_SET (comp : is_compact X) : iskfinite (X : hSet).
  Proof.
    set(φinv := is_z_isomorphism_mor (φiso comp)).
    set(idX := φinv (identity X)). (* identity X : X --> X *)
    set(idxx := pr12 idX).
    use(hinhuniv _ idxx).

    intros cob.      (* cob = (xᵢ , f) *)
    (* xᵢ is a K-finite subset of X such that colimIn filtCC xᵢ f = φinv (identity X) *)
    set(xᵢ := pr11 cob : kfinite_subtype (X : hSet)).
    set(f := pr21 cob : _ --> _). (* X -> xᵢ *)

    (* (coconeIn (kfinite_subsets_cocone X) xᵢ) ≡ pr1 : carrier_subset xᵢ -> X. *)
    apply(iskfinite_from_surjection (coconeIn (kfinite_subsets_cocone X) xᵢ)).
    - intro y; apply hinhpr.
      use make_hfiber.
      + exact(f y).
      + enough (Q : colimIn (homXX comp) xᵢ f = identity X)
          by exact(eqtohomot Q y).

        (* To prove Q observe that colimIn (homXX comp) xᵢ commutes with
           colimIn filtCC xᵢ · φ by the colimArrow property. *)
        assert (z : colimIn filtCC xᵢ · φ = colimIn (homXX comp) xᵢ)
          by apply colimArrowCommutes.

        apply(pathscomp0 (eqtohomot (!z) f)).
        change ((colimIn filtCC xᵢ · φ) f) with (φ (colimIn filtCC xᵢ f)).

        (* f is in the same equivalence class in filtCC as idX ≡ φinv (identity X). *)
        etrans. { apply maponpaths; exact(setquotl0 _ idX cob). }

        (* so φ (φinv (identity X)) = identity X. *)
        exact(eqtohomot (is_inverse_in_precat2 (φiso comp)) (identity X)).
    - exact(kfinite_subtype_property xᵢ).
  Qed.
End compact_sets_are_kfinite.
