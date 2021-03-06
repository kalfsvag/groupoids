Require Import HoTT.
Require Import HoTT.Categories.Functor.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
(* From GR.groupoid Require Import *)
(*      groupoid_quotient.gquot *)
(*      groupoid_quotient.gquot_functor *)
(*      groupoid_quotient.gquot_principles *)
(*      grpd_bicategory.grpd_bicategory *)
(*      path_groupoid.path_groupoid. *)
Require Import cquot cquot_functor cquot_principles cquot_poly path_category.

From GR.basics Require Import
     general.

Section Counit.
  Context `{Univalence}.

  Definition counit_map (X : 1 -Type)
    : one_types⟦cquot_functor(path_category X),X⟧.
  Proof.
    simple refine (cquot_rec X _ _ _ _) ; cbn.
    - exact idmap.
    - exact (fun _ _ => idmap).
    - reflexivity.
    - reflexivity.
  Defined.

  Definition naturality_help₁
             {X Y : one_types}
             (f : X -> Y)
             {a₁ a₂ : path_category X}
             (c : path_category X a₁ a₂)
    : path_over
        (fun h : cquot (path_category X) =>
           f (counit_map X h)
           =
           counit_map Y (cquot_functor_map (ap_functor f) h)
        )
        (ccleq (path_category X) c)
        idpath
        idpath.
  Proof.
    induction c.
    apply map_path_over.
    apply path_to_square.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    rewrite ce.
    reflexivity.
  Qed.

  Definition naturality_help₂
             {X Y : one_types}
             (f : X -> Y)
             {a₁ a₂ : path_category X}
             (c : path_category X a₁ a₂)
    : path_over
        (fun h : cquot (path_category X) =>
           counit_map Y (cquot_functor_map (ap_functor f) h)
           =
           f (counit_map X h)
        )
        (ccleq (path_category X) c)
        idpath
        idpath.
  Proof.
    induction c.
    apply map_path_over.
    apply path_to_square.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    rewrite ce.
    reflexivity.
  Qed.

  Definition counit_cq_naturality
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : forall (x : cquot_functor (path_category X)),
      (f · counit_map X) x = (counit_map Y · cquot_functor_map (ap_functor f)) x.
  Proof.
    simple refine (cquot_ind_set _ _ _ _).
    - reflexivity.
    - intros ? ? c.
      exact (naturality_help₁ f c).
  Defined.
  
  Definition counit_cq_naturality_inv
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : forall (x : cquot_functor (path_category X)),
      (counit_map Y · cquot_functor_map (ap_functor f)) x = (f · counit_map X) x.
  Proof.
    simple refine (cquot_ind_set _ _ _ _).
    - reflexivity.
    - intros ? ? c.
      exact (naturality_help₂ f c).
  Defined.

  Definition counit_cq_d
    : PseudoTransformation_d
        (lax_comp cquot_functor path_category_functor)
        (lax_id_functor one_types).
  Proof.
    make_pseudo_transformation.
    - exact counit_map.
    - intros X Y f.
      exact (path_forall _ _ (counit_cq_naturality f)).
    - intros X Y f.
      exact (path_forall _ _ (counit_cq_naturality_inv f)).
  Defined.

  Definition counit_cq_d_lax_naturality
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : laxnaturality_of_pd counit_cq_d f = path_forall _ _ (counit_cq_naturality f).
  Proof.
    exact idpath.
  Qed.
  
  Definition counit_cq_d_lax_naturality_inv
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : laxnaturality_of_inv_pd counit_cq_d f = path_forall _ _ (counit_cq_naturality_inv f).
  Proof.
    exact idpath.
  Qed.

  Definition comp_functor_path
             {X Y : one_types}
             (f c : one_types⟦X,Y⟧)
             (p : f ==> c)
    : lax_comp cquot_functor path_category_functor ₂ p
      =
      path_forall _ _ (cquot_functor_map_natural (ap_functor_natural p)).
  Proof.
    exact idpath.
  Qed.

  Definition comp_functor_Fid
             (X : one_types)
    : Fid (lax_comp cquot_functor path_category_functor) X
      =
      path_forall _ _ (fun x => (cquot_functor_map_id (path_category X) x)
                                  @ cquot_functor_map_natural (path_category_map_id X) x).
  Proof.
    rewrite path_forall_pp.
    reflexivity.
  Qed.

  Definition whisker_l_one_types
             {X Y Z : one_types}
             (f : one_types⟦Y,Z⟧)
             {g h : one_types⟦X,Y⟧}
             (α : g ==> h)
    : id₂ f * α = path_forall _ _ (fun x => ap f (ap10 α x)).
  Proof.
    cbn.
    f_ap.
    funext x.
    apply concat_1p.
  Qed.

  Definition whisker_r_one_types
             {X Y Z : one_types}
             (f : one_types⟦X,Y⟧)
             {g h : one_types⟦Y,Z⟧}
             (α : g ==> h)
    : α * id₂ f = path_forall _ _ (fun x => ap10 α (f x)).
  Proof.
    cbn.
    f_ap.
    funext x.
    apply concat_p1.
  Qed.

  Definition one_types_left_unit
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : left_unit f = idpath.
  Proof.
    exact idpath.
  Qed.

  Definition one_types_richt_unit
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : right_unit f = idpath.
  Proof.
    exact idpath.
  Qed.

  Definition one_types_left_unit_inv
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : left_unit_inv f = idpath.
  Proof.
    exact idpath.
  Qed.

  Definition one_types_right_unit_inv
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : right_unit_inv f = idpath.
  Proof.
    exact idpath.
  Qed.

  Definition one_types_assoc
             {W X Y Z : one_types}
             (h : one_types⟦Y,Z⟧) (g : one_types⟦X,Y⟧) (f : one_types⟦W,X⟧)
    : assoc h g f = idpath.
  Proof.
    exact idpath.
  Qed.

  Definition one_types_assoc_inv
             {W X Y Z : one_types}
             (h : one_types⟦Y,Z⟧) (g : one_types⟦X,Y⟧) (f : one_types⟦W,X⟧)
    : assoc_inv h g f = idpath.
  Proof.
    exact idpath.
  Qed.

  Definition vcomp_is_concat
             {X Y : one_types}
             {f g h : one_types⟦X,Y⟧}
             (α : f ==> g) (β : g ==> h)
    : β ∘ α = α @ β.
  Proof.
    exact idpath.
  Qed.

  Definition one_types_id₂
             {X Y : one_types}
             (f : one_types⟦X,Y⟧)
    : id₂ f = idpath.
  Proof.
    exact idpath.
  Qed.

  Definition path_forall_2
             {A B : Type}
             (f g : A -> B)
             (e₁ e₂ : f == g)
    : e₁ == e₂ -> path_forall f g e₁ = path_forall f g e₂
    := fun He => ap (path_forall f g) (path_forall e₁ e₂ He).

  Definition counit_cq_is_lax
    : is_pseudo_transformation_p counit_cq_d.
  Proof.
    make_is_pseudo_transformation.
    - intros X Y f g p.
      induction p.
      rewrite !vcomp_is_concat.
      rewrite (counit_cq_d_lax_naturality f).
      rewrite (comp_functor_path f).
      rewrite hcomp_id₂.
      rewrite one_types_id₂.
      rewrite concat_1p.
      rewrite (whisker_l_one_types (counit_cq_d Y)).
      rewrite <- !path_forall_pp.
      refine (path_forall_2 _ _ _ _ _).
      simple refine (cquot_ind_prop _ _ _).
      intros a.
      refine (_^ @ (concat_1p _)^).
      rewrite ap10_path_forall.
      exact (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _).
    - intros X.
      rewrite hcomp_id₂.
      rewrite !vcomp_is_concat, one_types_id₂.
      rewrite concat_1p.
      rewrite (counit_cq_d_lax_naturality (id₁ X)).
      rewrite (one_types_left_unit (counit_cq_d X)).
      rewrite one_types_right_unit_inv.
      rewrite !concat_1p.
      rewrite comp_functor_Fid.
      rewrite (whisker_l_one_types (counit_cq_d X)).
      refine (path_forall_2 _ _ _ _ _).
      simple refine (cquot_ind_prop _ _ _).
      intros a.
      refine (_ @ ap (ap (counit_cq_d X)) ((ap10_path_forall _ _ _ _)^)) ; cbn.
      rewrite ce.
      reflexivity.
    - intros X Y Z f g.
      rewrite !vcomp_is_concat.
      rewrite (whisker_r_one_types (counit_cq_d X)).
      rewrite (counit_cq_d_lax_naturality (g · f)).
      rewrite (counit_cq_d_lax_naturality g).
      rewrite (counit_cq_d_lax_naturality f).
      rewrite (one_types_assoc _ _ (counit_cq_d X)).
      rewrite (one_types_assoc_inv _ (counit_cq_d Y) _).
      rewrite !concat_1p.
      rewrite (whisker_l_one_types (counit_cq_d Z)).
      rewrite (whisker_l_one_types (Fmor (lax_id_functor one_types) Y Z g)).
      rewrite <- !path_forall_pp.
      refine (path_forall_2 _ _ _ _ _).
      simple refine (cquot_ind_prop _ _ _).
      intros a.
      cbn.
      rewrite <- path_forall_pp.
      rewrite !ap10_path_forall.
      rewrite !concat_1p ; simpl.
      rewrite ce.
      reflexivity.
    - intros X Y f.
      rewrite (counit_cq_d_lax_naturality f).
      rewrite (counit_cq_d_lax_naturality_inv f).
      rewrite vcomp_is_concat.
      rewrite one_types_id₂.
      rewrite <- path_forall_pp, <- path_forall_1.
      refine (path_forall_2 _ _ _ _ _).
      simple refine (cquot_ind_prop _ _ _).
      reflexivity.
    - intros X Y f.
      rewrite (counit_cq_d_lax_naturality f).
      rewrite (counit_cq_d_lax_naturality_inv f).
      rewrite vcomp_is_concat.
      rewrite one_types_id₂.
      rewrite <- path_forall_pp, <- path_forall_1.
      refine (path_forall_2 _ _ _ _ _).
      simple refine (cquot_ind_prop _ _ _).
      reflexivity.  
Qed.
  
  Definition counit_cq
    : PseudoTransformation
        (lax_comp cquot_functor path_category_functor)
        (lax_id_functor one_types)
    := Build_PseudoTransformation counit_cq_d counit_cq_is_lax.
End Counit.