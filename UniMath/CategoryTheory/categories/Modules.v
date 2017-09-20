(** Anthony Bordg, March-April 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Algebra.Modules.

(** ************************************************

Contents:

- Precategory of modules over a ring ([Mod])
- Category of modules over a ring ([category_Mod])
- Mod is a univalent category ([Mod_is_univalent])

***************************************************)


Section univalent_category_modules.

(** * The precategory of (left) R-modules and R-modules homomorphisms *)


Variable R : rng.

Definition precategory_ob_mor_module : precategory_ob_mor :=
   precategory_ob_mor_pair (module R) (λ M N, modulefun M N).

Local Open Scope Cat.

Definition islinear_id (M : precategory_ob_mor_module) : islinear (idfun (pr1module M)).
Proof.
  intros r x.
  unfold idfun. apply idpath.
Defined.

Definition ismodulefun_id (M : precategory_ob_mor_module) : ismodulefun (idfun (pr1module M)).
Proof.
  apply dirprodpair.
  - intros x y. apply idpath.
  - intros. apply  islinear_id.
Defined.

Definition modulefun_id : ∏ M : precategory_ob_mor_module, M --> M.
Proof.
  intro M.
  exists (idfun (pr1module M)).
  exact (ismodulefun_id M).
Defined.

Definition ismodulefun_comp {M N P : precategory_ob_mor_module} (f : M --> N) (g : N --> P) :
  ismodulefun (funcomp (pr1modulefun f) (pr1modulefun g)) :=
    dirprodpair (isbinopfuncomp (modulefun_to_binopfun f) (modulefun_to_binopfun g))
                (islinearfuncomp (modulefun_to_linearfun f) (modulefun_to_linearfun g)).

Definition modulefun_comp : ∏ M N P : precategory_ob_mor_module, M --> N → N --> P → M --> P.
Proof.
    intros  M N P f g.
    exists (funcomp (pr1modulefun f) (pr1modulefun g)).
    exact (ismodulefun_comp f g).
Defined.

Definition precategory_id_comp_module : precategory_id_comp (precategory_ob_mor_module) :=
  dirprodpair (modulefun_id) (modulefun_comp).

Definition precategory_data_module : precategory_data :=
   tpair _ (precategory_ob_mor_module) (precategory_id_comp_module).

Definition is_precategory_precategory_data_module : is_precategory (precategory_data_module).
Proof.
   apply dirprodpair.
   - apply dirprodpair.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun. intro x. apply idpath.
       * apply isapropismodulefun.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun. intro x. apply idpath.
       * apply isapropismodulefun.
   - intros M N P Q f g h.
     use total2_paths_f.
     + apply funextfun. intro x.
       unfold compose. cbn.
       rewrite funcomp_assoc.
       apply idpath.
     + apply isapropismodulefun.
Defined.

Definition Mod : precategory :=
   mk_precategory (precategory_data_module) (is_precategory_precategory_data_module).



(** ** The category of (left) R-modules and R-modules homomorphisms *)


(** The precategory of R-modules has homsets *)

Definition has_homsets_Mod : has_homsets Mod.
Proof.
   intros M N. unfold isaset. intros f g. unfold isaprop.
   apply (isofhlevelweqb 1 (total2_paths_equiv (λ x :  pr1module M ->  pr1module N, ismodulefun x) f g)).
   refine (isofhleveltotal2 1 _ _ _).
   - assert (p : isofhlevel 2 (pr1module M ->  pr1module N)).
     + apply impred. intro.
       exact (setproperty (pr1module N)).
     + exact (p (pr1 f) (pr1 g)).
   - intro p.
     assert (q : isaset (ismodulefun (pr1 g))).
     + exact (isasetaprop (isapropismodulefun (pr1 g))).
     + apply q.
Defined.

Definition category_Mod : category := category_pair Mod has_homsets_Mod.



(** *** The univalent category of (left) R-modules and R-modules homomorphisms *)


Definition moduleiso (M N : Mod) : UU := ∑ w : pr1module M ≃ pr1module N, ismodulefun w.

Definition moduleiso_to_modulefun (M N : Mod) : moduleiso M N -> modulefun M N.
Proof.
   intro f.
   exact (tpair _ (pr1weq (pr1 f)) (pr2 f)).
Defined.

Coercion moduleiso_to_modulefun : moduleiso >-> modulefun.

Definition pr1moduleiso {M N : Mod} (f : moduleiso M N) : (pr1module M) ≃ (pr1module N) := pr1 f.

Coercion pr1moduleiso : moduleiso >-> weq.

Definition moduleisopair {M N : Mod} (f : pr1module M ≃ pr1module N) (is : ismodulefun f) : moduleiso M N :=
   tpair _ f is.

Definition idmoduleiso (M : Mod) : moduleiso M M.
Proof.
   use moduleisopair.
   - exact (idweq (pr1module M)).
   - apply dirprodpair.
     + intros x y. apply idpath.
     + intros r x. apply idpath.
Defined.

Definition isbinopfuninvmap {M N : Mod} (f : moduleiso M N) : isbinopfun (invmap f).
Proof.
   intros x y.
   apply (invmaponpathsweq f).
   rewrite (homotweqinvweq f (op x y)).
   symmetry.
   transitivity (op ((pr1moduleiso f) (invmap f x)) ((pr1moduleiso f) (invmap f y))).
   apply (modulefun_to_isbinopfun f (invmap f x) (invmap f y)).
   rewrite 2 (homotweqinvweq f).
   apply idpath.
Defined.

Definition islinearinvmap {M N : Mod} (f : moduleiso M N) : islinear (invmap f).
Proof.
   intros r x.
   apply (invmaponpathsweq f).
   transitivity (module_mult N r x).
   exact (homotweqinvweq f (module_mult N r x)).
   transitivity (module_mult N r (pr1 f (invmap (pr1 f) x))).
   rewrite (homotweqinvweq (pr1 f) x).
   apply idpath.
   symmetry.
   apply (pr2 (pr2 f) r (invmap f x)).
Defined.

Definition invmoduleiso {M N : Mod} (f : moduleiso M N) : moduleiso N M.
Proof.
   use moduleisopair.
   - exact (invweq f).
   - apply dirprodpair.
     + exact (isbinopfuninvmap f).
     + exact (islinearinvmap f).
Defined.

Definition isaprop_islinear {M N : Mod} (f : (pr1module M) -> (pr1module N)) : isaprop (islinear f).
Proof.
   use impred. intro r.
   use impred. intro x.
   apply setproperty.
Defined.

Definition moduleiso' (M N : Mod) : UU := ∑ w : monoidiso (pr1module M) (pr1module N), islinear w.

Definition moduleiso_to_moduleiso' (M N : Mod) : moduleiso M N -> moduleiso' M N.
Proof.
   intro w.
   use tpair.
   - use tpair.
     + exact w.
     + use tpair.
       * exact (modulefun_to_isbinopfun w).
       * apply (modulefun_unel w).
   - exact (modulefun_to_islinear w).
Defined.

Definition moduleiso'_to_moduleiso (M N : Mod) : moduleiso' M N -> moduleiso M N.
Proof.
   intro w.
   use tpair.
   - exact (pr1 w).
   - apply dirprodpair.
     + exact (pr1 (pr2 (pr1 w))).
     + exact (pr2 w).
Defined.

Lemma modulefun_unel_uniqueness {M N : Mod} {f : pr1module M -> pr1module N} {is: ismodulefun f}
       (p : f (@unel (pr1module M)) = @unel (pr1module N)) : modulefun_unel (f,,is) = p.
Proof.
   apply (setproperty (pr1module N)).
Defined.

Definition moduleiso'_to_moduleiso_isweq (M N : Mod) : isweq (moduleiso'_to_moduleiso M N).
Proof.
   use (gradth _ (moduleiso_to_moduleiso' M N)). intro w.
   unfold moduleiso'_to_moduleiso, moduleiso_to_moduleiso'. cbn.
   rewrite (modulefun_unel_uniqueness (dirprod_pr2 (pr2 (pr1 w)))).
   apply idpath.
   intro w. apply idpath.
Defined.

Definition moduleiso'_to_moduleiso_weq (M N : Mod) : (moduleiso' M N) ≃ (moduleiso M N) :=
   weqpair (moduleiso'_to_moduleiso M N) (moduleiso'_to_moduleiso_isweq M N).

Lemma isaset_el_of_setwith2binop (X : setwith2binop) : isaset X.
Proof.
   intros x y.
   apply (setproperty X).
Defined.

Lemma isaprop_isrigfun {X Y : rig} (f : X -> Y) : isaprop (isrigfun f).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropismonoidfun.
  - apply isapropismonoidfun.
Defined.

Lemma isaset_rngfun (X Y : rng) : isaset (rngfun X Y).
Proof.
   apply (isofhleveltotal2 2).
   - use impred_isaset. intro x.
     apply isaset_el_of_setwith2binop.
   - intro f.
     apply (isasetaprop (isaprop_isrigfun f)).
Defined.

Definition modules_univalence_weq (M N : Mod) : (M ╝ N) ≃ (moduleiso' M N).
Proof.
   use weqbandf.
   - apply abgr_univalence.
   - intro e.
     use invweq.
     induction M. induction N. cbn in e. induction e.
     use weqimplimpl.
     + intro i.
       use total2_paths2_f.
       * use funextfun. intro r.
         use total2_paths2_f.
           apply funextfun. intro x. exact (i r x).
           apply isapropismonoidfun.
       * apply isaprop_isrigfun.
     + intro i. cbn.
       intros r x.
       unfold idmonoidiso. cbn in i.
       induction i.
       apply idpath.
     + apply isaprop_islinear.
     + apply isaset_rngfun.
Defined.

Definition modules_univalence_map (M N : Mod) : (M = N) -> (moduleiso M N).
Proof.
   intro p.
   induction p.
   exact (idmoduleiso M).
Defined.

Definition modules_univalence_map_isweq (M N : Mod) : isweq (modules_univalence_map M N).
Proof.
   use isweqhomot.
   - exact (weqcomp (weqcomp (total2_paths_equiv _ M N) (modules_univalence_weq M N)) (moduleiso'_to_moduleiso_weq M N)).
   - intro p.
     induction p.
     apply (pathscomp0 weqcomp_to_funcomp_app).
     apply idpath.
   - apply weqproperty.
Defined.

Definition modules_univalence (M N : Mod) : (M = N) ≃ (moduleiso M N).
Proof.
   use weqpair.
   - exact (modules_univalence_map M N).
   - exact (modules_univalence_map_isweq M N).
Defined.

(** Equivalence between isomorphisms and moduleiso in Mod R *)

Lemma iso_isweq {M N : ob Mod} (f : iso M N) : isweq (pr1 (pr1 f)).
Proof.
   use (gradth (pr1 (pr1 f))).
   - exact (pr1 (inv_from_iso f)).
   - intro x.
     set (T:= iso_inv_after_iso f).
     apply subtypeInjectivity in T.
     + set (T':= toforallpaths _ _ _ T).
       apply T'.
     + intro g.
       apply isapropismodulefun.
   - intro y.
     set (T:= iso_after_iso_inv f).
     apply subtypeInjectivity in T.
     + set (T':= toforallpaths _ _ _ T).
       apply T'.
     + intro g.
       apply isapropismodulefun.
Defined.

Lemma iso_moduleiso (M N : ob Mod) : iso M N -> moduleiso M N.
Proof.
   intro f.
   use moduleisopair.
   - use weqpair.
     + exact (pr1 (pr1 f)).
     + exact (iso_isweq f).
   - exact (pr2 (pr1 f)).
Defined.

Lemma moduleiso_is_iso {M N : ob Mod} (f : moduleiso M N) : @is_iso Mod M N (modulefunpair f (pr2 f)).
Proof.
   apply (is_iso_qinv (C:= Mod) _ (modulefunpair (invmoduleiso f) (pr2 (invmoduleiso f)))).
   split.
   - use total2_paths_f.
     + apply funextfun. intro x.
       unfold funcomp, idfun.
       apply homotinvweqweq.
     + apply isapropismodulefun.
   - use total2_paths_f.
     + apply funextfun. intro y.
       apply homotweqinvweq.
     + apply isapropismodulefun.
Defined.

Lemma moduleiso_iso (M N : ob Mod) : moduleiso M N -> iso M N.
Proof.
   intro f.
   use isopair.
   - use tpair.
     + exact f.
     + exact (pr2 f).
   - exact (moduleiso_is_iso f).
Defined.

Lemma moduleiso_iso_isweq (M N : ob Mod) : isweq (@moduleiso_iso M N).
Proof.
   apply (gradth _ (iso_moduleiso M N)).
   - intro f.
     apply subtypeEquality.
     + intro w.
       apply isapropismodulefun.
     + unfold moduleiso_iso, iso_moduleiso.
       use total2_paths_f.
       * apply idpath.
       * apply isapropisweq.
   - intro f.
     unfold iso_moduleiso, moduleiso_iso.
     use total2_paths_f.
     + apply idpath.
     + apply isaprop_is_iso.
Defined.

Definition moduleiso_iso_weq (M N : Mod) : (moduleiso M N) ≃ (iso M N) :=
   weqpair (moduleiso_iso M N) (moduleiso_iso_isweq M N).

Definition Mod_idtoiso_isweq : ∏ M N : ob Mod, isweq (fun p : M = N => idtoiso p).
Proof.
   intros M N.
   use (isweqhomot (weqcomp (modules_univalence M N) (moduleiso_iso_weq M N)) _).
   - intro p.
     induction p.
     use (pathscomp0 weqcomp_to_funcomp_app). cbn.
     use total2_paths_f.
     + apply idpath.
     + apply isaprop_is_iso.
   - apply weqproperty.
Defined.

Definition Mod_is_univalent : is_univalent Mod :=
  mk_is_univalent Mod_idtoiso_isweq has_homsets_Mod.

Definition univalent_category_Mod : univalent_category := mk_category Mod Mod_is_univalent.

End univalent_category_modules.
