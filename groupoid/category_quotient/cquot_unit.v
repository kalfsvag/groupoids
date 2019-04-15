Require Import HoTT.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
(* From GR.groupoid Require Import *)
(*      groupoid_quotient.gquot *)
(*      groupoid_quotient.gquot_functor *)
(*      groupoid_quotient.gquot_principles *)
(*      grpd_bicategory.grpd_bicategory *)
(*      path_groupoid.path_groupoid. *)
Require Import cquot cquot_functor cquot_principles path_category.

From GR.basics Require Import
     general.

Section Unit.
  Context `{Univalence}.

  Definition unit_map (C : PreCategory)
    : PreCat⟦C,path_category(cquot_functor C)⟧.
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
    - exact (ccl C).
    - exact (@ccleq C).
    - exact (@cconcat C).
    - exact (ce C).
  Defined.

  Definition unit_cq_1
             {C₁ C₂ : PreCategory}
             {x y : C₁}
             (F : Functor C₁ C₂)
             (c : morphism C₁ x y)
    : ap (cquot_functor_map F) (ccleq C₁ c) @ 1
      =
      1 @ ccleq C₂ (F _1 c)%morphism.
  Proof.
    exact ((concat_p1 _)
             @ (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)
             @ (concat_1p _)^).
  Qed.

  Definition unit_cq_2
             {C₁ C₂ : PreCategory}
             {x y : C₁}
             (F : Functor C₁ C₂)
             (c : morphism C₁ x y)
    : ccleq C₂ (F _1 c)%morphism @ 1
      =
      1 @ ap (cquot_functor_map F) (ccleq C₁ c).
  Proof.
    exact ((concat_p1 _)
             @ (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)^
             @ (concat_1p _)^).
  Qed.
  
  Definition unit_cq_d
    : PseudoTransformation_d
        (lax_id_functor PreCat)
        (lax_comp path_category_functor cquot_functor).
  Proof.
    make_pseudo_transformation.
    - exact unit_map.
    - intros C₁ C₂ F.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + reflexivity.
      + intros x y c.
        exact (unit_cq_1 F c).
    - intros C₁ C₂ F.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + reflexivity.
      + intros x y c.
        exact (unit_cq_2 F c).
  Defined.

  Definition unit_cq_is_lax
    : is_pseudo_transformation_p unit_cq_d.
  Proof.
    make_is_pseudo_transformation.
    - intros C₁ C₂ F₁ F₂ α.
      apply path_natural_transformation.
      intros x ; simpl.
      rewrite ap10_path_forall.
      rewrite !concat_1p, !concat_p1.
      reflexivity.
    - intros C.
      apply path_natural_transformation.
      intros x ; simpl.
      rewrite ap10_path_forall.
      rewrite ce.
      reflexivity.
    - intros C₁ C₂ C₃ F₁ F₂.
      apply path_natural_transformation.
      intro x ; simpl.
      rewrite ap10_path_forall.
      rewrite !ce.
      reflexivity.
    - intros C₁ C₂ F.
      apply path_natural_transformation.
      intros x ; simpl.
      reflexivity.
    - intros C₁ C₂ F.
      apply path_natural_transformation.
      intro ; reflexivity.
  Qed.

  Definition unit_cq
    : PseudoTransformation
        (lax_id_functor PreCat)
        (lax_comp path_category_functor cquot_functor)
    := Build_PseudoTransformation unit_cq_d unit_cq_is_lax.
End Unit.